module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.ChartLimitsInSchemes
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.AffineStageCharts
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.MorphismDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.ChartLimitsInSchemes

/-!
# Stacks 07SK over the limit of an inverse system of affine objects of the site

For a cofiltered inverse system of affine objects of the big fppf site presented by a cone
whose cone of underlying schemes is a limit, the three statements of Stacks 07SK, with no
cardinality hypothesis on the index category.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section AffineBaseDescent

/-! ### Transport along an isomorphism

The development below identifies the presheaf limit `CategoryTheory.Limits.limit` of the Yoneda
images of an inverse system of affine objects of the site with the Yoneda image of a given cone
point, and so needs to move each of the hypotheses of the descent argument across that
identification. The four lemmas of this subsection are exactly the transports used. -/

/-- **A cartesian square stays cartesian when its top edge is composed with an isomorphism and
its right edge is divided by the same one.** Paste the square whose vertical edges are the
identity and the inverse isomorphism on top of the given one. -/
private theorem isPullback_comp_iso {C : Type*} [Category* C] {P X X' Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} (e : X ≅ X') {f : X' ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd (e.hom ≫ f) g) : IsPullback (fst ≫ e.hom) snd f g := by
  have s : IsPullback (fst ≫ e.hom) (𝟙 P) e.inv fst := IsPullback.of_vert_isIso ⟨by simp⟩
  simpa using s.paste_vert h

/-- **The base change of an object along an isomorphism undoes pushing it forward along the same
one.** The square with identity top edge exhibits the given object as the fibre product. -/
private noncomputable def isoPullbackMapOfIsIso {C : Type*} [Category* C] [HasPullbacks C]
    {X X' : C} (u : X ⟶ X') [IsIso u] (Y : Over X) :
    Y ≅ (Over.pullback u).obj ((Over.map u).obj Y) :=
  Over.isoMk (IsPullback.isoPullback
    (IsPullback.of_horiz_isIso (fst := 𝟙 Y.left) (snd := Y.hom) (f := Y.hom ≫ u) (g := u)
      ⟨by simp⟩)) (by simp)

/-- **Base change along an isomorphism is faithful.** The first projection of the fibre product
along an isomorphism is itself an isomorphism, hence an epimorphism, and cancelling it recovers
the morphism of slices. -/
private theorem overPullback_map_injective_of_isIso {C : Type*} [Category* C] [HasPullbacks C]
    {X X' : C} (u : X ⟶ X') [IsIso u] {A A' : Over X'} (a b : A ⟶ A')
    (hab : (Over.pullback u).map a = (Over.pullback u).map b) : a = b := by
  have _ : IsIso (pullback.fst A.hom u) := (IsPullback.of_hasPullback A.hom u).isIso_fst_of_isIso
  have hleft : ((Over.pullback u).map a).left ≫ pullback.fst A'.hom u =
      ((Over.pullback u).map b).left ≫ pullback.fst A'.hom u := by rw [hab]
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst A.hom u)).mp
  simpa [Over.pullback_map_left, pullback.lift_fst] using hleft

/-- **The two ways of comparing a doubly iterated base change agree.** For a diagram of four
morphisms `aj, ai, bj, bi` out of two objects into two others, compatible with a morphism
`d : Xj ⟶ X` and a morphism `k` between the two sources, basing an object of `Over X` change
first along `d` and then along `aj` and `k`, in either order, gives the same comparison with the
single base change along `bi`. -/
private theorem iteratedBaseChangeIso_pentagon {C : Type*} [Category* C] [HasPullbacks C]
    {X Xj Bs L : C} (d : Xj ⟶ X) (aj : Bs ⟶ Xj) (ai : Bs ⟶ X) (bj : L ⟶ Xj) (bi : L ⟶ X)
    (k : L ⟶ Bs) (hd : aj ≫ d = ai) (hb : bj ≫ d = bi) (hkj : k ≫ aj = bj)
    (hki : k ≫ ai = bi) (Y : Over X) :
    (Over.pullback k).map (iteratedBaseChangeIso d aj ai hd Y).hom ≫
        (iteratedBaseChangeIso ai k bi hki Y).hom =
      (iteratedBaseChangeIso aj k bj hkj ((Over.pullback d).obj Y)).hom ≫
        (iteratedBaseChangeIso d bj bi hb Y).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [iteratedBaseChangeIso_hom_left, Over.pullback_map_left, Category.assoc]
  · exact (Over.w _).trans (Over.w _).symm

/-- **The compatibility square of the fullness statement descends along a base change by an
isomorphism.** Transporting a morphism of base changes along an isomorphism `k` of bases and
descending the resulting square back is the identity, because base change along `k` is faithful
and the comparison isomorphisms satisfy `iteratedBaseChangeIso_pentagon`. -/
private theorem comm_of_comm_of_pullback_isIso {C : Type*} [Category* C] [HasPullbacks C]
    {X Xj Bs L : C} (d : Xj ⟶ X) (aj : Bs ⟶ Xj) (ai : Bs ⟶ X) (bj : L ⟶ Xj) (bi : L ⟶ X)
    (k : L ⟶ Bs) [IsIso k] (hd : aj ≫ d = ai) (hb : bj ≫ d = bi) (hkj : k ≫ aj = bj)
    (hki : k ≫ ai = bi) (Y Z : Over X)
    (f : (Over.pullback ai).obj Y ⟶ (Over.pullback ai).obj Z)
    (g : (Over.pullback d).obj Y ⟶ (Over.pullback d).obj Z)
    (hcomm : (iteratedBaseChangeIso d bj bi hb Y).hom ≫
          (iteratedBaseChangeIso ai k bi hki Y).inv ≫ (Over.pullback k).map f ≫
            (iteratedBaseChangeIso ai k bi hki Z).hom =
        (Over.pullback bj).map g ≫ (iteratedBaseChangeIso d bj bi hb Z).hom) :
    (iteratedBaseChangeIso d aj ai hd Y).hom ≫ f =
      (Over.pullback aj).map g ≫ (iteratedBaseChangeIso d aj ai hd Z).hom := by
  have pentY := iteratedBaseChangeIso_pentagon d aj ai bj bi k hd hb hkj hki Y
  have pentZ := iteratedBaseChangeIso_pentagon d aj ai bj bi k hd hb hkj hki Z
  have natg := iteratedBaseChangeIso_naturality aj k bj hkj g
  have key : (Over.pullback k).map f =
      (iteratedBaseChangeIso ai k bi hki Y).hom ≫
        (iteratedBaseChangeIso ai k bi hki Y).inv ≫ (Over.pullback k).map f ≫
          (iteratedBaseChangeIso ai k bi hki Z).hom ≫
            (iteratedBaseChangeIso ai k bi hki Z).inv := by simp
  apply overPullback_map_injective_of_isIso k
  simp only [Functor.map_comp]
  rw [key, reassoc_of% pentY, reassoc_of% hcomm, ← reassoc_of% natg, ← reassoc_of% pentZ]
  simp

/-! ### The Yoneda image of an affine object of the site

The descent argument takes four hypotheses on its inverse system of presheaves. For a system of
Yoneda images of affine objects of the site all four hold with no cardinality hypothesis. -/

/-- The Yoneda image of an affine object of the big fppf site is an algebraic space. -/
private theorem isAlgebraicSpace_yoneda_inclusion (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicGeometry.BigAffineFppf B S hS) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS
      (yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj X)) :=
  AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _

/-- The Yoneda image of a morphism of affine objects of the big fppf site is an affine
morphism of algebraic spaces: the morphism of underlying schemes has affine source and target,
hence is an affine morphism of schemes. -/
private theorem isAffineHom_yoneda_inclusion (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicGeometry.BigAffineFppf B S hS}
    (f : X ⟶ Y) :
    AlgebraicGeometry.Space.IsAffineHom B S hS
      (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map f)) :=
  have : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj X)) := X.property
  have : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Y)) := Y.property
  AlgebraicGeometry.Space.isAffineHom_of_presheaf
    ((AlgebraicGeometry.Space.presheaf_yoneda_map_iff B S hS
        (P := @AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr
      (AlgebraicGeometry.isAffineHom_of_isAffine _))

/-- The Yoneda image of an affine object of the big fppf site is quasi-compact. -/
private theorem isQuasiCompactSpace_yoneda_inclusion (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicGeometry.BigAffineFppf B S hS) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj X)) :=
  AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _ X.property

/-- The Yoneda image of an affine object of the big fppf site is absolutely quasi-separated: an
affine scheme is a quasi-separated topological space. -/
private theorem isAbsolutelyQuasiSeparated_yoneda_inclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicGeometry.BigAffineFppf B S hS) :
    AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj X)) :=
  have : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj X)) := X.property
  isQuasiSeparated_yoneda B S hS hZ _ inferInstance

/-! ### The limit of an inverse system of affine objects of the site -/

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS)

/-- The inverse system of presheaves attached to an inverse system of affine objects of the big
fppf site: the Yoneda images of the underlying objects of the site. -/
private abbrev affineSystem : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (D ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS) ⋙ yoneda

variable (c : Cone D)
    (hc : IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c))

/-- **The comparison isomorphism.** A cone of affine objects of the site whose cone of
underlying schemes is a limit has its Yoneda image a limit of presheaves
(`AlgebraicGeometry.BigAffineFppf.isLimit_yoneda_mapCone`), so its vertex is canonically
isomorphic to the presheaf limit of the system. -/
private noncomputable def affineSystemLimitIso :
    limit (affineSystem B S hS D) ≅
      yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt) :=
  (limit.isLimit (affineSystem B S hS D)).conePointUniqueUpToIso
    (AlgebraicGeometry.BigAffineFppf.isLimit_yoneda_mapCone B S hS hc)

/-- The comparison isomorphism carries the projection of the given cone to the projection of the
presheaf limit. -/
private theorem affineSystemLimitIso_hom_comp (i : I) :
    (affineSystemLimitIso B S hS D c hc).hom ≫
        yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)) =
      limit.π (affineSystem B S hS D) i :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ i

/-- The inverse comparison isomorphism carries the projection of the presheaf limit to the
projection of the given cone. -/
private theorem affineSystemLimitIso_inv_comp (i : I) :
    (affineSystemLimitIso B S hS D c hc).inv ≫ limit.π (affineSystem B S hS D) i =
      yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ i

include c hc in
/-- The presheaf limit of the system is an algebraic space: it is isomorphic to the Yoneda image
of the given cone point. -/
private theorem isAlgebraicSpace_limit_affineSystem :
    AlgebraicGeometry.IsAlgebraicSpace B S hS (limit (affineSystem B S hS D)) :=
  isAlgebraicSpace_of_iso B S hS (affineSystemLimitIso B S hS D c hc).symm
    (isAlgebraicSpace_yoneda_inclusion B S hS c.pt)

include c hc in
/-- Every projection from the presheaf limit of the system is affine: up to the comparison
isomorphism it is the Yoneda image of a projection of the given cone. -/
private theorem isAffineHom_limitπ_affineSystem (i : I) :
    AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π (affineSystem B S hS D) i) := by
  rw [← affineSystemLimitIso_hom_comp B S hS D c hc i]
  exact isAffineHom_iso_comp (affineSystemLimitIso B S hS D c hc).hom
    (isAffineHom_yoneda_inclusion B S hS (c.π.app i))

include c hc in
/-- **The affine chart system over a stage has its limit computed in schemes.** This is the one
substantive fact, and for a system of affine objects of the site it needs no cardinality bound:
the chart system over the stage `i₀` is, stage by stage, the base change of the system along the
morphism of the site underlying `q₀`, so `isLimitOfCartesianCone` applies to the
given limiting cone of underlying schemes. Every morphism in sight is the Yoneda image of a
morphism of the site -- that is what makes `CategoryTheory.Functor.preimage` available here and
is the whole reason the affine case avoids the construction of the limit from a bound. -/
private noncomputable def chartLim_affineSystem
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS ((affineSystem B S hS D).map f))
    (i₀ : I) (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶
      (affineSystem B S hS D).obj i₀)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p : yoneda.obj U ⟶ limit (affineSystem B S hS D))
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π (affineSystem B S hS D) i₀) q₀) :
    IsLimit ((Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone
      (affineStageChartConeOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff U p q h)) := by
  classical
  have _ : PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  refine isLimitOfCartesianCone
    (D ⋙ AlgebraicGeometry.BigAffineFppf.toScheme B S hS)
    ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c) hc i₀
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀))
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (yoneda.preimage q₀)) _ _
    { app := fun j => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toStage)
      naturality := ?_ }
    { app := fun j => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toChart
      naturality := ?_ }
    ?_
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (p ≫ (affineSystemLimitIso B S hS D c hc).hom)))
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ?_ ?_ ?_
  · -- the projections to the stages are natural
    intro j k e
    have key : affineStageChartMapOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff e ≫
          yoneda.preimage
            (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff k).toStage =
        yoneda.preimage
            (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toStage ≫
          (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e.left) := by
      apply yoneda.map_injective
      simpa using
        affineStageChartMap_toStage_of_limitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff e
    simpa [affineStageChartOverDiagramOfLimitFacts] using
      congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map key
  · -- the projections to the chart over the stage `i₀` are natural
    intro j k e
    have key : affineStageChartMapOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff e ≫
          (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff k).toChart =
        (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toChart := by
      apply yoneda.map_injective
      simpa using
        affineStageChartMap_toChart_of_limitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff e
    simpa [affineStageChartOverDiagramOfLimitFacts] using
      congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map key
  · -- each stage of the chart system is cartesian over the stage of the system
    intro j
    have hsite : IsPullback
        (yoneda.preimage
          (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toStage)
        (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toChart
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map j.hom))
        (yoneda.preimage q₀) :=
      IsPullback.of_map_of_faithful yoneda (by
        simpa using
          (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).isPullback)
    exact hsite.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  · -- the vertex of the chart cone is cartesian over the vertex of the given cone
    have hsq : IsPullback (p ≫ (affineSystemLimitIso B S hS D c hc).hom) (yoneda.map q)
        (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)))
        q₀ := by
      refine isPullback_comp_iso (affineSystemLimitIso B S hS D c hc) ?_
      rwa [affineSystemLimitIso_hom_comp B S hS D c hc i₀]
    have hsite : IsPullback
        (yoneda.preimage (p ≫ (affineSystemLimitIso B S hS D c hc).hom)) q
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀))
        (yoneda.preimage q₀) :=
      IsPullback.of_map_of_faithful yoneda (by simpa using hsq)
    exact hsite.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  · -- the chart cone is compatible with the projections to the stages
    intro j
    have key :
        affineStageChartLiftOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff U p q h j ≫
          yoneda.preimage
            (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toStage =
        yoneda.preimage (p ≫ (affineSystemLimitIso B S hS D c hc).hom) ≫
          (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j.left) := by
      apply yoneda.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Category.assoc,
        affineSystemLimitIso_hom_comp B S hS D c hc j.left]
      simp [affineStageChartLiftOfLimitFacts]
    change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (affineStageChartLiftOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff U p q h
            j) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (yoneda.preimage
          (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toStage) =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (p ≫ (affineSystemLimitIso B S hS D c hc).hom)) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j.left))
    rw [← Functor.map_comp, ← Functor.map_comp, key]
  · -- the chart cone is compatible with the projection to the chart over `i₀`
    intro j
    have key :
        affineStageChartLiftOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff U p q h j ≫
          (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toChart =
            q := by
      apply yoneda.map_injective
      simp [affineStageChartLiftOfLimitFacts]
    change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (affineStageChartLiftOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff U p q h
            j) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (affineStageChartOfLimitFacts B S hS (affineSystem B S hS D) i₀ U₀ q₀ hAff j).toChart =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q
    rw [← Functor.map_comp, key]

include c hc in
/-- **The three facts the descent argument needs, for an inverse system of affine objects of the
big fppf site whose cone of underlying schemes is a limit.** No cardinality hypothesis on the
index category enters: the limit is handed to us as the cone `c`, and the comparison isomorphism
`affineSystemLimitIso` transports every statement about it to the presheaf limit. -/
private noncomputable def affineLimitFacts : LimitFacts B S hS (affineSystem B S hS D) where
  limAlg := isAlgebraicSpace_limit_affineSystem B S hS D c hc
  piAff := isAffineHom_limitπ_affineSystem B S hS D c hc
  chartLim := fun hAff i₀ U₀ q₀ U p q h =>
    chartLim_affineSystem B S hS D c hc hAff i₀ U₀ q₀ U p q h

/-! ### Stacks 07SK over the limit of an inverse system of affine objects of the site

The three statements of Stacks 07SK, for a cofiltered inverse system of affine objects of the
big fppf site presented by a cone whose cone of underlying schemes is a limit. The limit of the
system is the Yoneda image of the cone point, and no cardinality hypothesis on the index
category appears. -/

include hc in
/-- The finite-presentation hypothesis on an object over the Yoneda image of the cone point,
read on the presheaf limit of the system. -/
private theorem isFinitePresentation_comp_affineSystemLimitIso_inv
    {Y : Over (yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt))}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS
      ((Over.map (affineSystemLimitIso B S hS D c hc).inv).obj Y).hom :=
  IsFinitePresentation.of_isPullback B S hS hY hY
    (isAlgebraicSpace_limit_affineSystem B S hS D c hc)
    (isAlgebraicSpace_yoneda_inclusion B S hS c.pt)
    (IsPullback.of_horiz_isIso (fst := 𝟙 Y.left)
      (snd := Y.hom ≫ (affineSystemLimitIso B S hS D c hc).inv) (f := Y.hom)
      (g := (affineSystemLimitIso B S hS D c hc).hom) ⟨by simp⟩) hFp

include hZ hc in
/-- **Stacks 07SK, essential surjectivity, over the limit of a system of affine objects of the
site.** Every algebraic space of finite presentation over the Yoneda image of the cone point is
the base change of one over a stage. This is
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` with the cardinality bound on the
index category removed: the bound was only ever used to build the limit, and here the limit is
given. -/
public theorem exists_model_of_finitePresentation_affineBase
    (Y : Over (yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (yoneda.obj
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i)))),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).obj Yᵢ) := by
  classical
  obtain ⟨i, Yᵢ, hYᵢalg, hYᵢfp, ⟨e⟩⟩ := exists_model_of_finitePresentation_aux B S hS hZ
    (affineSystem B S hS D)
    (fun i => isAlgebraicSpace_yoneda_inclusion B S hS (D.obj i))
    (fun {_ _} f => isAffineHom_yoneda_inclusion B S hS (D.map f))
    (fun i => isQuasiCompactSpace_yoneda_inclusion B S hS (D.obj i))
    (fun i => isAbsolutelyQuasiSeparated_yoneda_inclusion B S hS hZ (D.obj i))
    (affineLimitFacts B S hS D c hc)
    ((Over.map (affineSystemLimitIso B S hS D c hc).inv).obj Y) hY
    (isFinitePresentation_comp_affineSystemLimitIso_inv B S hS D c hc hY hFp)
  exact ⟨i, Yᵢ, hYᵢalg, hYᵢfp,
    ⟨isoPullbackMapOfIsIso (affineSystemLimitIso B S hS D c hc).inv Y ≪≫
      (Over.pullback (affineSystemLimitIso B S hS D c hc).inv).mapIso e ≪≫
      iteratedBaseChangeIso (limit.π (affineSystem B S hS D) i)
        (affineSystemLimitIso B S hS D c hc).inv
        (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))
        (affineSystemLimitIso_inv_comp B S hS D c hc i) Yᵢ⟩⟩

include hc in
/-- **Stacks 07SK, faithfulness, over the limit of a system of affine objects of the site.** Two
morphisms of finite-presentation algebraic spaces over a stage that agree after base change to
the Yoneda image of the cone point already agree after base change to some later stage. This is
`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq` with the cardinality bound on the index
category removed. -/
public theorem eventually_eq_of_baseChange_eq_affineBase
    (i : I) (Yᵢ Zᵢ : Over (yoneda.obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i))))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).map f =
      (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).map f =
        (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).map g :=
  eventually_eq_of_baseChange_eq_aux B S hS (affineSystem B S hS D)
    (fun i => isAlgebraicSpace_yoneda_inclusion B S hS (D.obj i))
    (fun {_ _} a => isAffineHom_yoneda_inclusion B S hS (D.map a))
    (fun i => isQuasiCompactSpace_yoneda_inclusion B S hS (D.obj i))
    (affineLimitFacts B S hS D c hc) i Yᵢ Zᵢ hY hZ' hYfp hZfp f g
    (baseChange_eq_of_baseChange_eq
      (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))
      (affineSystemLimitIso B S hS D c hc).hom (limit.π (affineSystem B S hS D) i)
      (affineSystemLimitIso_hom_comp B S hS D c hc i) f g hfg)

include hZ hc in
/-- **Stacks 07SK, fullness, over the limit of a system of affine objects of the site.** A
morphism between base changes to the Yoneda image of the cone point of two finite-presentation
algebraic spaces over a stage comes from a morphism at some later stage. This is
`AlgebraicGeometry.Space.exists_morphism_after_baseChange` with the cardinality bound on the
index category removed. -/
public theorem exists_morphism_after_baseChange_affineBase
    (i : I) (Yᵢ Zᵢ : Over (yoneda.obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i))))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).obj Yᵢ ⟶
      (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).obj Yᵢ ⟶
        (Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).obj Zᵢ)
      (α : (Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j)))).obj
          ((Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).obj Yᵢ) ≅
        (Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).obj Yᵢ)
      (β : (Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j)))).obj
          ((Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).obj Zᵢ) ≅
        (Over.pullback (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i))) =
        pullback.fst ((Over.pullback (yoneda.map
              ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).obj Yᵢ).hom
            (yoneda.map
              ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j))) ≫
          pullback.fst Yᵢ.hom (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i))) =
        pullback.fst ((Over.pullback (yoneda.map
              ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))).obj Zᵢ).hom
            (yoneda.map
              ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j))) ≫
          pullback.fst Zᵢ.hom (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))) ∧
      α.hom ≫ f = (Over.pullback (yoneda.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j)))).map g ≫
        β.hom := by
  classical
  have hw : ∀ {j₁ j₂ : I} (a : j₁ ⟶ j₂),
      yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j₁)) ≫
          yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map a)) =
        yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j₂)) := by
    intro j₁ j₂ a
    rw [← Functor.map_comp, ← Functor.map_comp, c.w a]
  obtain ⟨j, e, g, α, β, hα, hβ, hcomm⟩ :=
    exists_morphism_after_baseChange_aux B S hS hZ (affineSystem B S hS D)
      (fun i => isAlgebraicSpace_yoneda_inclusion B S hS (D.obj i))
      (fun {_ _} a => isAffineHom_yoneda_inclusion B S hS (D.map a))
      (fun i => isQuasiCompactSpace_yoneda_inclusion B S hS (D.obj i))
      (fun i => isAbsolutelyQuasiSeparated_yoneda_inclusion B S hS hZ (D.obj i))
      (affineLimitFacts B S hS D c hc) i Yᵢ Zᵢ hY hZ' hYfp hZfp
      ((iteratedBaseChangeIso (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))
          (affineSystemLimitIso B S hS D c hc).hom (limit.π (affineSystem B S hS D) i)
          (affineSystemLimitIso_hom_comp B S hS D c hc i) Yᵢ).inv ≫
        (Over.pullback (affineSystemLimitIso B S hS D c hc).hom).map f ≫
        (iteratedBaseChangeIso (yoneda.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))
          (affineSystemLimitIso B S hS D c hc).hom (limit.π (affineSystem B S hS D) i)
          (affineSystemLimitIso_hom_comp B S hS D c hc i) Zᵢ).hom)
  rw [iteratedBaseChangeIso_unique _ _ _ (limit.w (affineSystem B S hS D) e) Yᵢ α hα,
    iteratedBaseChangeIso_unique _ _ _ (limit.w (affineSystem B S hS D) e) Zᵢ β hβ] at hcomm
  exact ⟨j, e, g,
    iteratedBaseChangeIso (yoneda.map
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))
      (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j)))
      (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))
      (hw e) Yᵢ,
    iteratedBaseChangeIso (yoneda.map
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (D.map e)))
      (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app j)))
      (yoneda.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)))
      (hw e) Zᵢ,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    comm_of_comm_of_pullback_isIso _ _ _ (limit.π (affineSystem B S hS D) j)
      (limit.π (affineSystem B S hS D) i) (affineSystemLimitIso B S hS D c hc).hom
      (hw e) (limit.w (affineSystem B S hS D) e)
      (affineSystemLimitIso_hom_comp B S hS D c hc j)
      (affineSystemLimitIso_hom_comp B S hS D c hc i) Yᵢ Zᵢ f g hcomm⟩

end AffineBaseDescent

end AlgebraicGeometry.Space

end
