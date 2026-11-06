module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLimitPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeClosedInFiniteFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraFinitePresentationColimitQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFinite
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# A finite morphism of algebraic spaces as a directed limit of finitely presented ones

A finite morphism `f : X ⟶ Y` of algebraic spaces over `S` with `Y` quasi-compact and
quasi-separated presents `X` as a directed inverse limit of algebraic spaces finite and of
finite presentation over `Y`, along closed immersions: Stacks 07VR.

The route is the one of the source.  The direct-image algebra `f_* 𝒪_X` is a finite
quasi-coherent `𝒪_Y`-algebra (`AlgebraicGeometry.Space.isFinite_pushforwardAlgebra_of_isFinite`);
Stacks 086Z writes it as a directed colimit of finite algebras of finite presentation with
surjective transition maps; and the anti-equivalence of Stacks 081V between the algebraic spaces
affine over `Y` and the quasi-coherent algebras on `Y` with fewer than `B.cutoff` sections over
every étale chart — `AlgebraicGeometry.Space.boundedAffineAlgebraAntiEquivalence`, which is
inhabited — turns that colimit into a limit of the relative spectra of the stages.  Every stage
is bounded because it is of finite type
(`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType`), and its relative
spectrum is finite and of finite presentation over `Y` because its direct image is the stage
(`AlgebraicGeometry.Space.isFinite_affineOver_of_isFinite_pushforwardAlgebra`,
`Space.isFinitePresentation_affineOver_of_isFinitePresentation_pushforwardAlgebra`).

## Main results

* `AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite`: **Stacks 07VR.**
* `AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite_of_presentation`: the limit
  presentation of `X` attached to a presentation of `f_* 𝒪_X` by finite algebras of finite
  presentation with surjective transition maps, its transition morphisms closed immersions.
* `AlgebraicGeometry.Space.nonempty_isLimit_affineOverToOver_of_mono`: a limit of spaces finite
  over `Y` along monomorphisms of spaces affine over `Y` is a limit of presheaves, along closed
  immersions.

## Implementation notes

The base module `StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitPresentation` carries
the same argument with the anti-equivalence and the presentation as hypotheses.  Its limit
argument — that a limit in the full subcategory of the algebraic spaces affine over `Y` is a
limit of presheaves when the transition morphisms are closed immersions, through the
scheme-theoretic image of Stacks 082X — is made of file-private lemmas, which are restated here
verbatim with the same proofs, because a private declaration cannot be used from another module
and that module's conditional registration must not be touched.

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

variable {B S hS}

/-- A morphism of spaces affine over `Y` commutes with the structure morphisms. -/
private theorem affineOver_hom_left_comp_hom {Y : AlgebraicSpaces B S hS}
    {X Z : AffineOver B S hS Y} (g : X ⟶ Z) :
    g.hom.left.hom ≫ Z.obj.hom.hom = X.obj.hom.hom :=
  congrArg (fun t => t.hom) (Over.w g.hom)

/-- Two morphisms of spaces affine over `Y` are equal when their underlying maps are. -/
private theorem affineOver_hom_ext {Y : AlgebraicSpaces B S hS} {X Z : AffineOver B S hS Y}
    {g h : X ⟶ Z} (H : g.hom.left.hom = h.hom.left.hom) : g = h := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact H

/-- **The limit of a cofiltered system of algebraic spaces finite over `Y`, along monomorphisms
of the spaces affine over `Y`, is computed in presheaves over `Y`, and its transition morphisms
are closed immersions.**

A monomorphism of spaces affine over `Y` with finite source is a monomorphism of presheaves (its
kernel pair is again affine over `Y`), and a finite monomorphism is a closed immersion.  The
limit is then computed in presheaves on each object of the site: restricting the system to the
slice over one index keeps the limit, the slice has a terminal object, and a compatible family
of morphisms out of a scheme of the site factors through the limit via the scheme-theoretic image
of Stacks 082X of its value at the terminal stage, which is finite over `Y` and lies in the range
of every transition morphism. -/
theorem nonempty_isLimit_affineOverToOver_of_mono {Y : AlgebraicSpaces B S hS}
    {J : Type v} [Category.{w} J] [IsCofiltered J] (D : J ⥤ AffineOver B S hS Y)
    (c : Cone D) (hc : IsLimit c)
    (hcfin : IsFinite B S hS c.pt.obj.hom.hom)
    (hfin : ∀ i, IsFinite B S hS (D.obj i).obj.hom.hom)
    (hmono : ∀ {i j : J} (g : i ⟶ j), Mono (D.map g)) :
    Nonempty (IsLimit ((affineOverToOver B S hS Y).mapCone c)) ∧
      ∀ {i j : J} (g : i ⟶ j), IsClosedImmersion B S hS (D.map g).hom.left.hom := by
  classical
  have affineOverToOver_map_left : ∀ {X Z : AffineOver B S hS Y} (g : X ⟶ Z),
      ((affineOverToOver B S hS Y).map g).left = g.hom.left.hom := by
    intro X Z g
    exact rfl
  have evaluationComp_map : ∀ {J : Type (max v w)} [Category.{w} J] (D : J ⥤ AffineOver B S hS Y)
      (U : BigFppfOver B S hS) {i j : J} (g : i ⟶ j),
      (((D ⋙ affineOverToOver B S hS Y) ⋙ Over.forget Y.obj) ⋙
        (evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (op U)).map g =
      (D.map g).hom.left.hom.app (op U) := by
    intro J _ D U i j g
    exact rfl
  have isFinite_hom_of_affineOver : ∀ {X Z : AffineOver B S hS Y} (g : X ⟶ Z)
      (_hX : IsFinite B S hS X.obj.hom.hom) (_hZ : IsFinite B S hS Z.obj.hom.hom),
      IsFinite B S hS g.hom.left.hom := by
    intro X Z g hX hZ
    refine isFinite_of_comp_of_isSeparated B S hS g.hom.left.hom Z.obj.hom.hom ?_ ?_
    · simpa only [← ObjectProperty.FullSubcategory.comp_hom, Over.w] using hX
    · exact isSeparated_of_isFinite B S hS Z.obj.hom.hom Z.obj.left.property Y.property hZ
  have mono_hom_left_hom : ∀ {X Z : AffineOver B S hS Y} (g : X ⟶ Z) [Mono g]
      (_hX : IsFinite B S hS X.obj.hom.hom) (_hZ : IsFinite B S hS Z.obj.hom.hom),
      Mono g.hom.left.hom := by
    intro X Z g _ hX hZ
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
  have isClosedImmersion_of_isFinite_of_mono :
      ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [Mono f]
      (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
      (_hf : IsFinite B S hS f), IsClosedImmersion B S hS f := by
    intro X Y f _ hX hY hf
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
  have mono_π_of_isTerminal : ∀ {J : Type (max v w)} [Category.{w} J]
      {D : J ⥤ AffineOver B S hS Y} {c : Cone D}
      (_hc : IsLimit c) {i₀ : J} (hi₀ : IsTerminal i₀) (_hm : ∀ i, Mono (D.map (hi₀.from i))),
      Mono (c.π.app i₀) := by
    intro J _ D c hc i₀ hi₀ hm
    refine ⟨fun {Z} a b hab => hc.hom_ext (fun i => ?_)⟩
    have := hm i
    apply (cancel_mono (D.map (hi₀.from i))).mp
    simpa only [Category.assoc, c.w] using hab
  have exists_lift_of_isTerminal : ∀ {J : Type (max v w)} [Category.{w} J]
      (D : J ⥤ AffineOver B S hS Y)
      (c : Cone D) (_hc : IsLimit c) {i₀ : J} (hi₀ : IsTerminal i₀)
      (_hfin : ∀ i, IsFinite B S hS (D.obj i).obj.hom.hom)
      (_hclosed : ∀ i, IsClosedImmersion B S hS (D.map (hi₀.from i)).hom.left.hom)
      (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ Y.obj)
      (a : (Functor.const J).obj (Over.mk q) ⟶ D ⋙ affineOverToOver B S hS Y),
      ∃ l : Over.mk q ⟶ (affineOverToOver B S hS Y).obj c.pt,
        ∀ i, l ≫ (affineOverToOver B S hS Y).map (c.π.app i) = a.app i := by
    intro J _ D c hc i₀ hi₀ hfin hclosed U q a
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
        have hn := a.naturality (hi₀.from i)
        exact hn.symm.trans (Category.id_comp _)
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
      have hw := affineOver_hom_left_comp_hom (D.map (hi₀.from i))
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
        affineOver_hom_left_comp_hom L
      rw [Category.assoc, hw, ← Category.assoc, hpι]
      exact Over.w (a.app i₀)
    · apply Over.OverMorphism.ext
      show (p ≫ L.hom.left.hom) ≫ (c.π.app i).hom.left.hom = (a.app i).left
      have hl : L.hom.left.hom ≫ (c.π.app i).hom.left.hom = b i :=
        congrArg (fun t : W ⟶ D.obj i => t.hom.left.hom) (hc.fac (Cone.mk W b') i)
      rw [Category.assoc, hl]
      exact hpb i
  have isLimit_affineOverToOver_of_isTerminal : ∀ {J : Type (max v w)} [Category.{w} J]
      (D : J ⥤ AffineOver B S hS Y)
      (c : Cone D) (_hc : IsLimit c) {i₀ : J} (hi₀ : IsTerminal i₀)
      (_hcfin : IsFinite B S hS c.pt.obj.hom.hom)
      (_hfin : ∀ i, IsFinite B S hS (D.obj i).obj.hom.hom)
      (_hclosed : ∀ i, IsClosedImmersion B S hS (D.map (hi₀.from i)).hom.left.hom),
      Nonempty (IsLimit ((affineOverToOver B S hS Y).mapCone c)) := by
    intro J _ D c hc i₀ hi₀ hcfin hfin hclosed
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
      have hw := affineOver_hom_left_comp_hom (D.map (hi₀.from i))
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
  have hclosed : ∀ {i j : J} (g : i ⟶ j), IsClosedImmersion B S hS (D.map g).hom.left.hom := by
    intro i j g
    have := hmono g
    have : Mono (D.map g).hom.left.hom := mono_hom_left_hom (D.map g) (hfin i) (hfin j)
    exact isClosedImmersion_of_isFinite_of_mono (D.map g).hom.left.hom
      (D.obj i).obj.left.property (D.obj j).obj.left.property
      (isFinite_hom_of_affineOver (D.map g) (hfin i) (hfin j))
  refine ⟨?_, hclosed⟩
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨h⟩ := isLimit_affineOverToOver_of_isTerminal (Over.forget i₀ ⋙ D)
    (c.whisker (Over.forget i₀))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)
    (Over.mkIdTerminal (X := i₀)) hcfin (fun i => hfin i.left) (fun i => hclosed _)
  exact ⟨Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀)
    ((affineOverToOver B S hS Y).mapCone c) h⟩

variable (B S hS)

/-! ### Stacks 07VR, from a presentation of the direct-image algebra -/

/-- **A finite morphism is the limit of the relative spectra of a presentation of its
direct-image algebra.**  Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over `S`, and
let `f_* 𝒪_X` be written as a directed colimit of finite quasi-coherent `𝒪_Y`-algebras of finite
presentation with locally surjective transition maps.  Then `X` is the directed limit of the
relative spectra of the stages, which are finite and of finite presentation over `Y`, along
closed immersions.

This is the argument of Stacks 07VR after its appeal to Stacks 086Z, with no hypothesis beyond the
presentation: the anti-equivalence it runs through is
`AlgebraicGeometry.Space.boundedAffineAlgebraAntiEquivalence`, which is inhabited, and every
stage is bounded because it is of finite type
(`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType`). -/
theorem exists_integralFiniteSystem_of_isFinite_of_presentation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hfin : IsFinite B S hS f)
    (hpres : ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS ⟨Y, hY⟩)
      (φ : D ⟶ (Functor.const I).obj ((quasicoherentPushforwardAlgebraFunctor B S hS ⟨Y, hY⟩).obj
        (op ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := ⟨X, hX⟩)
          (Y := ⟨Y, hY⟩) f), hfin.isAffineHom⟩))),
      Nonempty (IsColimit (Cocone.mk _ φ)) ∧
      (∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
      ∀ i j (h : i ≤ j), Presheaf.IsLocallySurjective
        (SmallEtale.topology B S hS Y) (D.map (homOfLE h)).hom.right.hom) :
    ∃ s : IntegralFiniteSystem B S hS f,
      letI := s.indexPreorder
      ∀ (i j : s.indexType) (h : i ≤ j),
        IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op) := by
  classical
  set Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩ with hY'
  set X' : AlgebraicSpaces B S hS := ⟨X, hX⟩ with hX'
  set E := boundedAffineAlgebraAntiEquivalence B S hS with hE
  set Z : AffineOver B S hS Y' :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := X') (Y := Y') f),
      hfin.isAffineHom⟩ with hZ
  set Ab : BoundedQuasicoherentAlgebra B S hS Y' := (E.pushforward Y').obj (op Z) with hAb
  have hZfin : IsFinite B S hS Z.obj.hom.hom := hfin
  obtain ⟨I, hIpre, hIne, hIdir, D, φ, ⟨hcolim⟩, hDprops, hDsurj⟩ := hpres
  let _ : Preorder I := hIpre
  let _ : Nonempty I := hIne
  let _ : IsDirected I (· ≤ ·) := hIdir
  set Db : I ⥤ BoundedQuasicoherentAlgebra B S hS Y' :=
    boundedLift D (fun i => (hDprops i).1.isFiniteType) with hDb
  set cb : Cocone Db := boundedCocone D (fun i => (hDprops i).1.isFiniteType) Ab φ with hcbdef
  have hcblim : IsColimit cb :=
    isColimitBoundedCocone D (fun i => (hDprops i).1.isFiniteType) Ab φ hcolim
  set EQ := E.equivalence Y' with hEQ
  set F' := EQ.symm.leftOp.functor with hF'
  set DA : Iᵒᵖ ⥤ AffineOver B S hS Y' := Db.op ⋙ F' with hDA
  have hstageEq : ∀ i : I, DA.obj (op i) =
      E.relativeSpec (D.obj i)
        (AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType B S hS _ (hDprops i).1.isFiniteType) :=
    fun _ => rfl
  have hlim0 : IsLimit (F'.mapCone cb.op) := isLimitOfPreserves F' hcblim.op
  set eA := (E.pushforwardIso Y').app (op Z) with heA
  set eZ : Z ≅ (F'.mapCone cb.op).pt :=
    ((EQ.unitIso.app (op Z)) ≪≫ EQ.inverse.mapIso eA).unop.symm with heZ
  set c0 := F'.mapCone cb.op with hc0
  set cu : Cone DA := c0.extend eZ.hom with hcu
  have hculim : IsLimit cu :=
    IsLimit.ofIsoLimit hlim0 (Cone.ext eZ.symm (fun j => by
      show c0.π.app j = eZ.inv ≫ eZ.hom ≫ c0.π.app j
      rw [← Category.assoc, eZ.inv_hom_id, Category.id_comp]))
  have hDAfin : ∀ i : Iᵒᵖ, IsFinite B S hS (DA.obj i).obj.hom.hom := by
    intro i
    obtain ⟨i⟩ := i
    rw [hstageEq i]
    exact isFinite_affineOver_of_isFinite_pushforwardAlgebra B S hS _
      (AlgebraSheaf.IsFinite.of_iso (E.relativeSpecPushforwardIso (D.obj i) _).symm
        (hDprops i).1)
  have hDAfp : ∀ i : Iᵒᵖ, IsFinitePresentation B S hS (DA.obj i).obj.hom.hom := by
    intro i
    obtain ⟨i⟩ := i
    rw [hstageEq i]
    exact isFinitePresentation_affineOver_of_isFinitePresentation_pushforwardAlgebra B S hS _
      (AlgebraSheaf.IsFinitePresentation.of_iso
        (E.relativeSpecPushforwardIso (D.obj i) _).symm (hDprops i).2)
  have hDAmono : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), Mono (DA.map g) := by
    intro i j g
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    have hle : j ≤ i := leOfHom g.unop
    have hgeq : homOfLE hle = g.unop := homOfLE_leOfHom _
    have hepi : Epi (D.map g.unop) := by
      rw [← hgeq]
      have hls : Sheaf.IsLocallySurjective (D.map (homOfLE hle)).hom.right := hDsurj j i hle
      have hepi' : Epi (D.map (homOfLE hle)).hom.right := inferInstance
      refine ⟨fun {Z} p r hpr => ?_⟩
      apply ObjectProperty.hom_ext
      apply AlgebraSheaf.Hom.ext
      exact (cancel_epi (D.map (homOfLE hle)).hom.right).mp
        (congrArg (fun t => t.hom.right) hpr)
    have hepib : Epi (Db.map g.unop) :=
      Functor.epi_of_epi_map (boundedQuasicoherentAlgebraInclusion B S hS Y') hepi
    have hd : DA.map g = F'.map ((Db.map g.unop).op) := rfl
    rw [hd]
    exact F'.map_mono _
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  obtain ⟨⟨hpre⟩, hclosed⟩ :=
    nonempty_isLimit_affineOverToOver_of_mono DA cu hculim hZfin hDAfin hDAmono
  refine ⟨
    { indexType := I
      diagram := DA ⋙ affineOverToOver B S hS Y' ⋙ Over.forget Y'.obj
      structureMap :=
        { app := fun i => (DA.obj i).obj.hom.hom
          naturality := fun i j g => by
            show (DA.map g).hom.left.hom ≫ (DA.obj j).obj.hom.hom =
              (DA.obj i).obj.hom.hom ≫ 𝟙 Y'.obj
            rw [Category.comp_id]
            exact affineOver_hom_left_comp_hom (DA.map g) }
      limitCone :=
        { app := fun i => (cu.π.app i).hom.left.hom
          naturality := fun i j g => by
            have h := congrArg (fun t : Z ⟶ DA.obj j => t.hom.left.hom) (cu.w g)
            simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] at h
            show 𝟙 X ≫ (cu.π.app j).hom.left.hom =
              (cu.π.app i).hom.left.hom ≫ (DA.map g).hom.left.hom
            rw [Category.id_comp]
            exact h.symm }
      compatible := fun i => by
        exact (affineOver_hom_left_comp_hom (cu.π.app i)).symm
      isLimit := isLimitOfPreserves (Over.forget Y'.obj) hpre
      stageAlgebraicSpace := fun i => (DA.obj i).obj.left.property
      stageFinite := hDAfin
      stageFinitePresentation := hDAfp }, ?_⟩
  intro i j h
  exact hclosed (homOfLE h).op


/-- **Stacks 07VR.** Let `S` be a scheme and let `f : X ⟶ Y` be a finite morphism of algebraic
spaces over `S`, with `Y` quasi-compact and quasi-separated.  Then `X` is the limit of a directed
inverse system of algebraic spaces `X_i`, finite and of finite presentation over `Y`, whose
transition morphisms are closed immersions.

The direct-image algebra `f_* 𝒪_X` is a finite quasi-coherent `𝒪_Y`-algebra
(`AlgebraicGeometry.Space.isFinite_pushforwardAlgebra_of_isFinite`); Stacks 086Z
(`Space.exists_directed_isFinite_isFinitePresentation_locallySurjective_of_isFinite`)
writes it as a directed colimit of finite algebras of finite presentation with surjective
transition maps; and `X_i = \underline{Spec}_Y(𝒜_i)` is the limit presentation by
`AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite_of_presentation`. -/
theorem exists_integralFiniteSystem_of_isFinite {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hfin : IsFinite B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ s : IntegralFiniteSystem B S hS f,
      letI := s.indexPreorder
      ∀ (i j : s.indexType) (h : i ≤ j),
        IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op) := by
  refine exists_integralFiniteSystem_of_isFinite_of_presentation B S hS f hX hY hfin ?_
  exact exists_directed_isFinite_isFinitePresentation_locallySurjective_of_isFinite B S hS ⟨Y, hY⟩ _
    hYqc hYqs (isFinite_pushforwardAlgebra_of_isFinite B S hS _ hfin)


end AlgebraicGeometry.Space

end
