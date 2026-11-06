module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLimitPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# A finite morphism of algebraic spaces as a directed limit of finitely presented ones

A finite morphism `f : X ⟶ Y` of algebraic spaces over `S` with `Y` quasi-compact and
quasi-separated presents `X` as a directed inverse limit of algebraic spaces finite and of
finite presentation over `Y`.  The route is the one of Stacks 07VR: the direct-image algebra
`f_* 𝒪_X` is a finite quasi-coherent `𝒪_Y`-algebra, Stacks 086Z writes it as a directed colimit
of finite algebras of finite presentation with surjective transition maps, and the
anti-equivalence of Stacks 081V turns that colimit into a limit of the relative spectra of the
stages.

## Main results

* `AlgebraicGeometry.Space.integralFiniteSystem_of_isFinite`: **Stacks 07VR**, the inverse
  system, in the shape `AlgebraicGeometry.Space.IntegralFiniteSystem` in which Stacks 07VS
  consumes it.

## Implementation notes

The two inputs of the source proof are carried, because neither is available: the
anti-equivalence of Stacks 081V between the algebraic spaces affine over a base and the
quasi-coherent algebras on it is the structure
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, which this library deliberately leaves
uninhabited, and the colimit presentation of Stacks 086Z is stated nowhere.  A third hypothesis
is the affine-chart comparison between finiteness of a morphism and finiteness of its
direct-image algebra, in the three instances in which the proof uses it; Stacks 07VR takes that
comparison as immediate from the construction of the relative spectrum of Stacks 081W, which
this library's `AlgebraicGeometry.Space.relativeSpec` does not carry, being defined through the
anti-equivalence alone.

What is *not* carried is the statement that `X` is the limit, which is the conclusion.  The
anti-equivalence turns the algebra colimit into a limit in the category of algebraic spaces
affine over `Y`, but a limit in that full subcategory need not be a limit of presheaves; that it
is, here, is the file-local `isLimit_affineOverToOver`, and it is where the
closed-immersion hypothesis on the transition morphisms is used.  Presheaf limits are computed
on each object of the big site, so what has to be produced is a factorisation of a compatible
family of morphisms out of a scheme `U`, and the factorisation runs through the
scheme-theoretic image of Stacks 082X of `U` in a fixed stage: that image is a closed subspace
of a space finite over `Y`, hence finite over `Y` and so affine over `Y`, and minimality of the
image puts it inside the range of every transition morphism.

The index type of the carried colimit lives in `Type u`, the universe of the values of the
site's presheaves, which is what `AlgebraicGeometry.Space.IntegralFiniteSystem` records and what
the library's other colimit presentations of algebras are stated with.

The transition morphisms are closed immersions because the algebra maps are locally surjective,
hence epimorphisms, hence monomorphisms after the anti-equivalence; a monomorphism of algebraic
spaces affine over `Y` with finite source has monomorphic underlying morphism of presheaves, and
a finite monomorphism is a closed immersion.

## References

* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w v' w'

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finiteness and monomorphisms in the affine slice -/

variable {B S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FiniteMorphismLimitPresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FiniteMorphismLimitPresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private lemma affineOverToOver_map_left {Y : AlgebraicSpaces B S hS}
    {X Z : AffineOver B S hS Y} (g : X ⟶ Z) :
    ((affineOverToOver B S hS Y).map g).left = g.hom.left.hom := rfl

private lemma diagramForget_map {Y : AlgebraicSpaces B S hS} {J : Type v} [Category.{w} J]
    (D : J ⥤ AffineOver B S hS Y) {i j : J} (g : i ⟶ j) :
    (D ⋙ affineOverToOver B S hS Y ⋙ Over.forget Y.obj).map g = (D.map g).hom.left.hom := rfl

private lemma evaluationComp_map {Y : AlgebraicSpaces B S hS} {J : Type v} [Category.{w} J]
    (D : J ⥤ AffineOver B S hS Y) (U : BigFppfOver B S hS) {i j : J} (g : i ⟶ j) :
    (((D ⋙ affineOverToOver B S hS Y) ⋙ Over.forget Y.obj) ⋙
        (evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (op U)).map g =
      (D.map g).hom.left.hom.app (op U) := rfl

/-- A morphism in the affine slice commutes with the structure morphisms to `Y`. -/
private lemma affineOver_hom_left_hom_comp {Y : AlgebraicSpaces B S hS}
    {X Z : AffineOver B S hS Y} (g : X ⟶ Z) :
    g.hom.left.hom ≫ Z.obj.hom.hom = X.obj.hom.hom :=
  congrArg (fun t => t.hom) (Over.w g.hom)

/-- Two morphisms in the affine slice are equal once their underlying presheaf maps are. -/
private lemma affineOver_hom_ext {Y : AlgebraicSpaces B S hS}
    {X Z : AffineOver B S hS Y} {g h : X ⟶ Z} (e : g.hom.left.hom = h.hom.left.hom) : g = h := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact e

/-- A morphism of algebraic spaces affine over `Y` whose source is finite over `Y` is itself
finite, because the target is separated over `Y`. -/
private theorem isFinite_hom_of_affineOver {Y : AlgebraicSpaces B S hS}
    {X Z : AffineOver B S hS Y} (g : X ⟶ Z)
    (hX : IsFinite B S hS X.obj.hom.hom) (hZ : IsFinite B S hS Z.obj.hom.hom) :
    IsFinite B S hS g.hom.left.hom := by
  refine isFinite_of_comp_of_isSeparated B S hS g.hom.left.hom Z.obj.hom.hom ?_ ?_
  · simpa only [affineOver_hom_left_hom_comp] using hX
  · exact isSeparated_of_isFinite B S hS Z.obj.hom.hom Z.obj.left.property Y.property hZ

/-- A monomorphism of algebraic spaces affine over `Y` with finite source has monomorphic
underlying morphism of presheaves: the two projections of the fibre product of the morphism with
itself are again affine over `Y`, so they are identified by the cancellation property. -/
private theorem mono_hom_left_hom {Y : AlgebraicSpaces B S hS}
    {X Z : AffineOver B S hS Y} (g : X ⟶ Z) [Mono g]
    (hX : IsFinite B S hS X.obj.hom.hom) (hZ : IsFinite B S hS Z.obj.hom.hom) :
    Mono g.hom.left.hom := by
  set k : X.obj.left.obj ⟶ Z.obj.left.obj := g.hom.left.hom with hk
  have hpb : IsAlgebraicSpace B S hS (pullback k k) :=
    isAlgebraicSpace_pullback B S hS k k X.obj.left.property X.obj.left.property
      Z.obj.left.property
  set W : AlgebraicSpaces B S hS := ⟨pullback k k, hpb⟩ with hW
  set a : W ⟶ X.obj.left := ObjectProperty.homMk (pullback.fst k k) with ha
  set b : W ⟶ X.obj.left := ObjectProperty.homMk (pullback.snd k k) with hb
  have hbfin : IsFinite B S hS b.hom :=
    isFinite_pullback_snd B S hS k k
      (isFinite_hom_of_affineOver g hX hZ)
  have hWfin : IsFinite B S hS (b ≫ X.obj.hom).hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      isFinite_comp B S hS hbfin hX
  set W' : AffineOver B S hS Y := ⟨Over.mk (b ≫ X.obj.hom), hWfin.isAffineHom⟩ with hW'
  have hab : a ≫ X.obj.hom = b ≫ X.obj.hom := by
    rw [← Over.w g.hom]
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ha, hb, ObjectProperty.homMk_hom]
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  set a' : W' ⟶ X := ObjectProperty.homMk (Over.homMk a hab) with ha'
  set b' : W' ⟶ X := ObjectProperty.homMk (Over.homMk b) with hb'
  have he : a' = b' := by
    refine (cancel_mono g).mp (affineOver_hom_ext ?_)
    show pullback.fst k k ≫ k = pullback.snd k k ≫ k
    exact pullback.condition
  have he' : pullback.fst k k = pullback.snd k k :=
    congrArg (fun t : W' ⟶ X => t.hom.left.hom) he
  refine ⟨fun {T} p q hpq => ?_⟩
  calc
    p = pullback.lift p q hpq ≫ pullback.fst k k := (pullback.lift_fst p q hpq).symm
    _ = pullback.lift p q hpq ≫ pullback.snd k k := by rw [he']
    _ = q := pullback.lift_snd p q hpq

/-- A finite monomorphism of algebraic spaces over `S` is a closed immersion: finiteness makes
it representable, and the base changes to schemes are finite monomorphisms, hence closed
immersions. -/
@[sga "3 V 4.1.3" "more general"]
private theorem isClosedImmersion_of_isFinite_of_mono
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [Mono f]
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFinite B S hS f) : IsClosedImmersion B S hS f := by
  have hr := (isFinite_iff_representable B S hS f hX hY).mp hf
  refine ⟨hr.1, ?_⟩
  intro U V g a p hp
  have : Mono (yoneda.map p) := by
    have := hp.isLimit
    exact PullbackCone.mono_snd_of_is_pullback_of_mono hp.isLimit
  have : Mono p := yoneda.mono_of_mono_map inferInstance
  have hfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map p) := hr.2.property g a p hp
  have : Mono ((BigFppfOver.toScheme B S hS).map p) :=
    (BigFppfOver.toScheme B S hS).map_mono p
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨hfin, inferInstance⟩


/-! ### The limit of a system of affine spaces over `Y`, computed in presheaves -/

/-- The projection of a limit cone to a terminal index is a monomorphism as soon as every
morphism to that index is one. -/
private theorem mono_π_of_isTerminal {C : Type v} [Category.{w} C] {J : Type v'}
    [Category.{w'} J] {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {i₀ : J}
    (hi₀ : IsTerminal i₀) (hm : ∀ i, Mono (D.map (hi₀.from i))) : Mono (c.π.app i₀) := by
  refine ⟨fun {Z} a b hab => hc.hom_ext (fun i => ?_)⟩
  have := hm i
  apply (cancel_mono (D.map (hi₀.from i))).mp
  simpa only [Category.assoc, c.w] using hab

/-- A compatible family of morphisms from a scheme of the site into a system of algebraic spaces
finite over `Y`, whose transition morphisms to a terminal index are closed immersions, factors
through the limit of the system.

The scheme-theoretic image of the morphism to the terminal stage is a closed subspace of that
stage finite over `Y`, hence itself affine over `Y`; it is contained in the range of every
transition morphism by minimality, which produces a cone over the system with that image as
vertex, and the limit property supplies the factorisation. -/
private theorem exists_lift_of_isTerminal {Y : AlgebraicSpaces B S hS}
    {J : Type v} [Category.{w} J] (D : J ⥤ AffineOver B S hS Y)
    (c : Cone D) (hc : IsLimit c) {i₀ : J} (hi₀ : IsTerminal i₀)
    (hfin : ∀ i, IsFinite B S hS (D.obj i).obj.hom.hom)
    (hclosed : ∀ i, IsClosedImmersion B S hS (D.map (hi₀.from i)).hom.left.hom)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ Y.obj)
    (a : (Functor.const J).obj (Over.mk q) ⟶ D ⋙ affineOverToOver B S hS Y) :
    ∃ l : Over.mk q ⟶ (affineOverToOver B S hS Y).obj c.pt,
      ∀ i, l ≫ (affineOverToOver B S hS Y).map (c.π.app i) = a.app i := by
  classical
  set M : Subfunctor (D.obj i₀).obj.left.obj :=
    schemeTheoreticImageSubfunctor B S hS (a.app i₀).left with hM
  have hMclosed : IsClosedSubspace B S hS M :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (a.app i₀).left
      (D.obj i₀).obj.left.property
  set r : ∀ i : J, (D.obj i).obj.left.obj ⟶ (D.obj i₀).obj.left.obj :=
    fun i => (D.map (hi₀.from i)).hom.left.hom with hr
  have hmono : ∀ i : J, Mono (r i) := fun i =>
    mono_of_isClosedImmersion B S hS _ (hclosed i)
  have ha : ∀ i : J, (a.app i).left ≫ r i = (a.app i₀).left := fun i => by
    simp only [hr]
    have h2 : a.app i ≫ (affineOverToOver B S hS Y).map (D.map (hi₀.from i)) = a.app i₀ := by
      have h1 := a.naturality (hi₀.from i)
      simp only [Functor.const_obj_map, Category.id_comp, Functor.comp_map] at h1
      exact h1.symm
    have h3 := congrArg (fun t => t.left) h2
    rw [Over.comp_left] at h3
    exact h3
  have hMle : ∀ i : J, M ≤ Subfunctor.range (r i) := fun i => by
    refine schemeTheoreticImageSubfunctor_le B S hS _
      (isClosedSubspace_range_of_isClosedImmersion B S hS _ (D.obj i).obj.left.property
        (hclosed i)) ?_
    rw [← ha i]
    exact Subfunctor.range_comp_le _ _
  have hiso : ∀ i : J, IsIso (Subfunctor.toRange (r i)) := fun i => by
    have := hmono i
    infer_instance
  set b : ∀ i : J, M.toFunctor ⟶ (D.obj i).obj.left.obj :=
    fun i => Subfunctor.homOfLe (hMle i) ≫ inv (Subfunctor.toRange (r i)) with hb
  have hbr : ∀ i : J, b i ≫ r i = M.ι := fun i => by
    have he : inv (Subfunctor.toRange (r i)) ≫ r i = (Subfunctor.range (r i)).ι := by
      apply (cancel_epi (Subfunctor.toRange (r i))).mp
      simpa only [IsIso.hom_inv_id_assoc] using (Subfunctor.toRange_ι (r i)).symm
    rw [hb]
    rw [Category.assoc, he, Subfunctor.homOfLe_ι]
  have hbY : ∀ i : J, b i ≫ (D.obj i).obj.hom.hom = M.ι ≫ (D.obj i₀).obj.hom.hom := fun i => by
    have hw : r i ≫ (D.obj i₀).obj.hom.hom = (D.obj i).obj.hom.hom :=
      affineOver_hom_left_hom_comp (D.map (hi₀.from i))
    calc
      b i ≫ (D.obj i).obj.hom.hom = b i ≫ r i ≫ (D.obj i₀).obj.hom.hom := by rw [hw]
      _ = (b i ≫ r i) ≫ (D.obj i₀).obj.hom.hom := (Category.assoc _ _ _).symm
      _ = M.ι ≫ (D.obj i₀).obj.hom.hom := by rw [hbr i]
  set Ms : AlgebraicSpaces B S hS := ⟨M.toFunctor, hMclosed.1⟩ with hMs
  have hWfin : IsFinite B S hS (M.ι ≫ (D.obj i₀).obj.hom.hom) :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS M.ι hMclosed.2) (hfin i₀)
  set W : AffineOver B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := Ms) (Y := Y)
      (M.ι ≫ (D.obj i₀).obj.hom.hom)), hWfin.isAffineHom⟩ with hW
  set b' : (Functor.const J).obj W ⟶ D :=
    { app := fun i => ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (b i))
        (by apply ObjectProperty.hom_ext; exact hbY i))
      naturality := fun i j g => by
        refine affineOver_hom_ext ?_
        show b j = b i ≫ (D.map g).hom.left.hom
        have := hmono j
        apply (cancel_mono (r j)).mp
        rw [hbr j, Category.assoc]
        have hrj : (D.map g).hom.left.hom ≫ r j = r i := by
          show (D.map g ≫ D.map (hi₀.from j)).hom.left.hom = r i
          rw [← D.map_comp, hi₀.hom_ext (g ≫ hi₀.from j) (hi₀.from i)]
        rw [hrj, hbr i] } with hb'
  set L : W ⟶ c.pt := hc.lift (Cone.mk W b') with hL
  set p : yoneda.obj U ⟶ M.toFunctor :=
    toSchemeTheoreticImage B S hS (a.app i₀).left with hp
  have hpι : p ≫ M.ι = (a.app i₀).left := toSchemeTheoreticImage_ι B S hS _
  have hpb : ∀ i : J, p ≫ b i = (a.app i).left := fun i => by
    have := hmono i
    apply (cancel_mono (r i)).mp
    rw [Category.assoc, hbr i, hpι]
    exact (ha i).symm
  refine ⟨Over.homMk (p ≫ L.hom.left.hom) ?_, fun i => ?_⟩
  · show (p ≫ L.hom.left.hom) ≫ (c.pt).obj.hom.hom = q
    have hw : L.hom.left.hom ≫ (c.pt).obj.hom.hom = M.ι ≫ (D.obj i₀).obj.hom.hom :=
      affineOver_hom_left_hom_comp L
    rw [Category.assoc, hw, ← Category.assoc, hpι]
    exact Over.w (a.app i₀)
  · apply Over.OverMorphism.ext
    show (p ≫ L.hom.left.hom) ≫ (c.π.app i).hom.left.hom = (a.app i).left
    have hl : L.hom.left.hom ≫ (c.π.app i).hom.left.hom = b i :=
      congrArg (fun t : W ⟶ D.obj i => t.hom.left.hom) (hc.fac (Cone.mk W b') i)
    rw [Category.assoc, hl]
    exact hpb i


/-- The limit of a system of algebraic spaces affine over `Y`, over an index category with a
terminal object, is computed in presheaves over `Y`: limits of presheaves are computed on each
object of the site, and a compatible family of sections over an object is a compatible family of
morphisms out of that object, which factors uniquely through the limit by
`AlgebraicGeometry.Space.exists_lift_of_isTerminal`. -/
private theorem isLimit_affineOverToOver_of_isTerminal {Y : AlgebraicSpaces B S hS}
    {J : Type v} [Category.{w} J] (D : J ⥤ AffineOver B S hS Y)
    (c : Cone D) (hc : IsLimit c) {i₀ : J} (hi₀ : IsTerminal i₀)
    (hcfin : IsFinite B S hS c.pt.obj.hom.hom)
    (hfin : ∀ i, IsFinite B S hS (D.obj i).obj.hom.hom)
    (hclosed : ∀ i, IsClosedImmersion B S hS (D.map (hi₀.from i)).hom.left.hom) :
    Nonempty (IsLimit ((affineOverToOver B S hS Y).mapCone c)) := by
  classical
  have hconn : IsConnected J := isConnected_of_isTerminal J hi₀
  have hmonoD : ∀ i : J, Mono (D.map (hi₀.from i)) := fun i => by
    have := mono_of_isClosedImmersion B S hS _ (hclosed i)
    refine ⟨fun {W} p q hpq => affineOver_hom_ext ?_⟩
    apply (cancel_mono (D.map (hi₀.from i)).hom.left.hom).mp
    exact congrArg (fun t : W ⟶ D.obj i₀ => t.hom.left.hom) hpq
  have hmonoπ : Mono (c.π.app i₀) := mono_π_of_isTerminal hc hi₀ hmonoD
  have hmono0 : Mono (c.π.app i₀).hom.left.hom :=
    mono_hom_left_hom (c.π.app i₀) hcfin (hfin i₀)
  refine ⟨isLimitOfReflects (Over.forget Y.obj) ?_⟩
  apply evaluationJointlyReflectsLimits
  intro Uop
  obtain ⟨U⟩ := Uop
  apply Classical.choice
  apply (Types.isLimit_iff _).mpr
  intro s hs
  have hx : ∀ {i j : J} (g : i ⟶ j),
      ((D.map g).hom.left.hom.app (op U)) (s i) = s j := by
    intro i j g
    have h := hs g
    rw [evaluationComp_map D U g] at h
    exact h
  set e : ∀ i : J, yoneda.obj U ⟶ (D.obj i).obj.left.obj :=
    fun i => yonedaEquiv.symm (s i) with he
  have hse : ∀ i : J, yonedaEquiv (e i) = s i := fun i => by
    simp only [he]
    exact yonedaEquiv.apply_symm_apply _
  have hec : ∀ {i j : J} (g : i ⟶ j), e i ≫ (D.map g).hom.left.hom = e j := by
    intro i j g
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, hse i, hse j]
    exact hx g
  set q : yoneda.obj U ⟶ Y.obj := e i₀ ≫ (D.obj i₀).obj.hom.hom with hq
  have heq : ∀ i : J, e i ≫ (D.obj i).obj.hom.hom = q := fun i => by
    have hw : (D.map (hi₀.from i)).hom.left.hom ≫ (D.obj i₀).obj.hom.hom =
        (D.obj i).obj.hom.hom :=
      affineOver_hom_left_hom_comp (D.map (hi₀.from i))
    rw [hq, ← hw, ← Category.assoc, hec]
  set a : (Functor.const J).obj (Over.mk q) ⟶ D ⋙ affineOverToOver B S hS Y :=
    { app := fun i => Over.homMk (e i) (heq i)
      naturality := fun i j g => by
        apply Over.OverMorphism.ext
        rw [Over.comp_left, Over.comp_left]
        simp only [Over.id_left, Functor.const_obj_map, Functor.comp_map]
        exact (hec g).symm } with hadef
  obtain ⟨l, hl⟩ := exists_lift_of_isTerminal D c hc hi₀ hfin hclosed U q a
  have hl' : ∀ i : J, l.left ≫ (c.π.app i).hom.left.hom = e i := fun i => by
    have h := congrArg (fun t => t.left) (hl i)
    rw [Over.comp_left] at h
    simp only [hadef, affineOverToOver_map_left] at h
    exact h
  have hx' : ∀ i : J,
      ((c.π.app i).hom.left.hom.app (op U)) (yonedaEquiv l.left) = s i := fun i => by
    have h3 : yonedaEquiv (l.left ≫ (c.π.app i).hom.left.hom) = s i := by
      rw [hl' i]
      exact hse i
    have h2 := yonedaEquiv_comp (X := U) (F := (c.pt).obj.left.obj)
      (G := (D.obj i).obj.left.obj) l.left (c.π.app i).hom.left.hom
    exact h2.symm.trans h3
  refine ⟨yonedaEquiv l.left, fun i => ?_, fun y hy => ?_⟩
  · show ((c.π.app i).hom.left.hom.app (op U)) (yonedaEquiv l.left) = s i
    exact hx' i
  · have hy' : ∀ i : J, ((c.π.app i).hom.left.hom.app (op U)) y = s i := fun i => hy i
    have hm : Mono ((c.π.app i₀).hom.left.hom.app (op U)) := inferInstance
    exact (mono_iff_injective ((c.π.app i₀).hom.left.hom.app (op U))).mp hm
      ((hy' i₀).trans (hx' i₀).symm)

/-- The limit of a cofiltered system of algebraic spaces affine over `Y` with closed-immersion
transition morphisms is computed in presheaves over `Y`: restricting the system to the slice
category over one index is a restriction along an initial functor, which preserves the limit,
and that slice has a terminal object. -/
private theorem isLimit_affineOverToOver {Y : AlgebraicSpaces B S hS}
    {J : Type v} [Category.{w} J] [IsCofiltered J] (D : J ⥤ AffineOver B S hS Y)
    (c : Cone D) (hc : IsLimit c)
    (hcfin : IsFinite B S hS c.pt.obj.hom.hom)
    (hfin : ∀ i, IsFinite B S hS (D.obj i).obj.hom.hom)
    (hclosed : ∀ {i j : J} (g : i ⟶ j), IsClosedImmersion B S hS (D.map g).hom.left.hom) :
    Nonempty (IsLimit ((affineOverToOver B S hS Y).mapCone c)) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨h⟩ := isLimit_affineOverToOver_of_isTerminal (Over.forget i₀ ⋙ D)
    (c.whisker (Over.forget i₀))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)
    (Over.mkIdTerminal (X := i₀)) hcfin (fun i => hfin i.left) (fun i => hclosed _)
  exact ⟨Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀)
    ((affineOverToOver B S hS Y).mapCone c) h⟩


/-! ### Stacks 07VR -/

/-- An equivalence of categories preserves monomorphisms: its inverse is faithful, and the
inverse's value on the image of a morphism is that morphism conjugated by the unit. -/
private theorem mono_equivalence_functor_map {C : Type v} [Category.{w} C] {Dc : Type v'}
    [Category.{w'} Dc] (e : C ≌ Dc) {X Z : C} (h : X ⟶ Z) [Mono h] :
    Mono (e.functor.map h) := by
  refine e.inverse.mono_of_mono_map (f := e.functor.map h) ?_
  have hn := e.unitIso.hom.naturality h
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hm : Mono (e.unitIso.hom.app X ≫ e.inverse.map (e.functor.map h)) := by
    rw [← hn]
    exact mono_comp _ _
  have hk : e.inverse.map (e.functor.map h) =
      inv (e.unitIso.hom.app X) ≫
        (e.unitIso.hom.app X ≫ e.inverse.map (e.functor.map h)) := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hk]
  exact mono_comp _ _

/-- A morphism of quasi-coherent algebras which is locally surjective on sections is an
epimorphism, because a morphism of algebra sheaves is determined by its underlying morphism of
sheaves of rings. -/
private theorem epi_of_isLocallySurjective {Y : AlgebraicSpaces B S hS}
    {A C : QuasicoherentAlgebra B S hS Y} (g : A ⟶ C)
    (hg : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.obj) g.hom.right.hom) :
    Epi g := by
  have hls : Sheaf.IsLocallySurjective g.hom.right := hg
  have hepi : Epi g.hom.right := inferInstance
  refine ⟨fun {Z} p r hpr => ?_⟩
  apply ObjectProperty.hom_ext
  apply AlgebraSheaf.Hom.ext
  exact (cancel_epi g.hom.right).mp (congrArg (fun t : A ⟶ Z => t.hom.right) hpr)

variable (B S hS)

/-- **Stacks 07VR.** A finite morphism `f : X ⟶ Y` of algebraic spaces over `S` with `Y`
quasi-compact and quasi-separated presents `X` as a directed inverse limit of algebraic spaces
finite and of finite presentation over `Y`.

The direct-image algebra `f_* 𝒪_X` is a finite quasi-coherent `𝒪_Y`-algebra, so `h086Z` writes
it as a directed colimit of finite algebras of finite presentation with surjective transition
maps.  Applying the anti-equivalence `E` turns that colimit into a limit of the relative spectra
`X_i = \underline{Spec}_Y(𝒜_i)`; the surjections become monomorphisms, hence closed immersions
between spaces finite over `Y`, and the limit is computed in presheaves by
`AlgebraicGeometry.Space.isLimit_affineOverToOver`. -/
@[no_expose, stacks 07VR "granted `E`, the anti-equivalence of Stacks 081V between the \
algebraic spaces affine over a base and the quasi-coherent algebras on it, which this \
library states as a \
structure with no inhabitant; `h086Z`, the conclusion of Stacks 086Z that a finite \
quasi-coherent algebra on a quasi-compact quasi-separated algebraic space is a directed \
colimit of finite algebras of finite presentation with locally surjective transition maps; and \
`hPushforwardIsFinite`, `hRelativeSpecIsFinite`, `hRelativeSpecIsFinitePresentation`, the \
affine-chart comparison between finiteness of a morphism and finiteness of its direct-image \
algebra, which the source takes as immediate from the construction of the relative spectrum of \
Stacks 081W. `E` and `h086Z` conclude about categories and about algebras, and the comparison \
is about a single morphism, so none of them is the universally quantified form of this \
conclusion"]
def integralFiniteSystem_of_isFinite {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hfin : IsFinite B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (E : AffineAlgebraAntiEquivalence B S hS)
    (hPushforwardIsFinite : ∀ {Y' : AlgebraicSpaces B S hS} (Z : AffineOver B S hS Y'),
      IsFinite B S hS Z.obj.hom.hom → ((E.pushforward Y').obj (op Z)).obj.IsFinite)
    (hRelativeSpecIsFinite : ∀ {Y' : AlgebraicSpaces B S hS}
      (A : QuasicoherentAlgebra B S hS Y'), A.obj.IsFinite →
      IsFinite B S hS (relativeSpec B S hS E A).obj.hom.hom)
    (hRelativeSpecIsFinitePresentation : ∀ {Y' : AlgebraicSpaces B S hS}
      (A : QuasicoherentAlgebra B S hS Y'), A.obj.IsFinite → A.obj.IsFinitePresentation →
      IsFinitePresentation B S hS (relativeSpec B S hS E A).obj.hom.hom)
    (h086Z : ∀ (Y' : AlgebraicSpaces B S hS) (A : QuasicoherentAlgebra B S hS Y'),
      IsQuasiCompactSpace B S hS Y'.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.obj →
      A.obj.IsFinite →
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : I ⥤ QuasicoherentAlgebra B S hS Y') (φ : D ⟶ (Functor.const I).obj A),
        Nonempty (IsColimit (Cocone.mk A φ)) ∧
        (∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
        ∀ i j (h : i ≤ j), Presheaf.IsLocallySurjective
          (SmallEtale.topology B S hS Y'.obj) (D.map (homOfLE h)).hom.right.hom) :
    IntegralFiniteSystem B S hS f := by
  classical
  refine Classical.choice ?_
  set Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩ with hY'
  set X' : AlgebraicSpaces B S hS := ⟨X, hX⟩ with hX'
  set Z : AffineOver B S hS Y' :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := X') (Y := Y') f),
      hfin.isAffineHom⟩ with hZ
  set A : QuasicoherentAlgebra B S hS Y' := (E.pushforward Y').obj (op Z) with hA
  have hZfin : IsFinite B S hS Z.obj.hom.hom := hfin
  have hAfin : A.obj.IsFinite := hPushforwardIsFinite Z hZfin
  obtain ⟨I, hIpre, hIne, hIdir, D, φ, ⟨hcolim⟩, hDprops, hDsurj⟩ := h086Z Y' A hYqc hYqs hAfin
  let _ : Preorder I := hIpre
  let _ : Nonempty I := hIne
  let _ : IsDirected I (· ≤ ·) := hIdir
  set EQ := E.equivalence Y' with hEQ
  set F' := EQ.symm.leftOp.functor with hF'
  set DA : Iᵒᵖ ⥤ AffineOver B S hS Y' := D.op ⋙ F' with hDA
  have hstageEq : ∀ i : I, DA.obj (op i) = relativeSpec B S hS E (D.obj i) := fun _ => rfl
  have hlim0 : IsLimit (F'.mapCone (Cocone.mk A φ).op) := isLimitOfPreserves F' hcolim.op
  set eA := (E.pushforwardIso Y').app (op Z) with heA
  set eZ : Z ≅ (F'.mapCone (Cocone.mk A φ).op).pt :=
    ((EQ.unitIso.app (op Z)) ≪≫ EQ.inverse.mapIso eA).unop.symm with heZ
  set c0 := F'.mapCone (Cocone.mk A φ).op with hc0
  set cu : Cone DA := c0.extend eZ.hom with hcu
  have hculim : IsLimit cu :=
    IsLimit.ofIsoLimit hlim0 (Cone.ext eZ.symm (fun j => by
      change c0.π.app j = eZ.inv ≫ eZ.hom ≫ c0.π.app j
      rw [← Category.assoc, eZ.inv_hom_id, Category.id_comp]))
  have hDAfin : ∀ i : Iᵒᵖ, IsFinite B S hS (DA.obj i).obj.hom.hom := by
    intro i
    obtain ⟨i⟩ := i
    exact hRelativeSpecIsFinite (D.obj i) (hDprops i).1
  have hDAfp : ∀ i : Iᵒᵖ, IsFinitePresentation B S hS (DA.obj i).obj.hom.hom := by
    intro i
    obtain ⟨i⟩ := i
    exact hRelativeSpecIsFinitePresentation (D.obj i) (hDprops i).1 (hDprops i).2
  have hDAclosed : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      IsClosedImmersion B S hS (DA.map g).hom.left.hom := by
    intro i j g
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    have hle : j ≤ i := leOfHom g.unop
    have hgeq : homOfLE hle = g.unop := homOfLE_leOfHom _
    have hepi : Epi (D.map g.unop) := by
      rw [← hgeq]
      exact epi_of_isLocallySurjective (D.map (homOfLE hle)) (hDsurj j i hle)
    have hmonoop : Mono ((D.map g.unop).op) := inferInstance
    have hmono : Mono (DA.map g) := by
      have hd : DA.map g = F'.map ((D.map g.unop).op) := rfl
      rw [hd]
      exact mono_equivalence_functor_map EQ.symm.leftOp ((D.map g.unop).op)
    have hmono' : Mono (DA.map g).hom.left.hom :=
      mono_hom_left_hom (DA.map g) (hDAfin (op i)) (hDAfin (op j))
    exact isClosedImmersion_of_isFinite_of_mono (DA.map g).hom.left.hom
      (DA.obj (op i)).obj.left.property (DA.obj (op j)).obj.left.property
      (isFinite_hom_of_affineOver (DA.map g) (hDAfin (op i)) (hDAfin (op j)))
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  obtain ⟨hpre⟩ := isLimit_affineOverToOver DA cu hculim hZfin hDAfin hDAclosed
  exact ⟨
    { indexType := I
      diagram := DA ⋙ affineOverToOver B S hS Y' ⋙ Over.forget Y'.obj
      structureMap :=
        { app := fun i => (DA.obj i).obj.hom.hom
          naturality := fun i j g => by
            have h := congrArg (fun t => t.hom) (Over.w (DA.map g).hom)
            rw [ObjectProperty.FullSubcategory.comp_hom] at h
            change (DA.map g).hom.left.hom ≫ (DA.obj j).obj.hom.hom =
              (DA.obj i).obj.hom.hom ≫ 𝟙 Y'.obj
            rw [Category.comp_id]
            exact h }
      limitCone :=
        { app := fun i => (cu.π.app i).hom.left.hom
          naturality := fun i j g => by
            have h := congrArg (fun t : Z ⟶ DA.obj j => t.hom.left.hom) (cu.w g)
            simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] at h
            change 𝟙 X ≫ (cu.π.app j).hom.left.hom =
              (cu.π.app i).hom.left.hom ≫ (DA.map g).hom.left.hom
            rw [Category.id_comp]
            exact h.symm }
      compatible := fun i => by
        have h := congrArg (fun t => t.hom) (Over.w (cu.π.app i).hom)
        rw [ObjectProperty.FullSubcategory.comp_hom] at h
        exact h.symm
      isLimit := isLimitOfPreserves (Over.forget Y'.obj) hpre
      stageAlgebraicSpace := fun i => (DA.obj i).obj.left.property
      stageFinite := hDAfin
      stageFinitePresentation := hDAfp }⟩

end AlgebraicGeometry.Space

end
