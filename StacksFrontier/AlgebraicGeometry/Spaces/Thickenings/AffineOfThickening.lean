module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.Theorem
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import
  StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageDescentChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SchemeStageChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionCollections
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceSmoothPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfFiniteOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LimitChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NoetherianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.AffineOfAffine

/-!
# A thickening of an affine algebraic space is affine

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`. If `G` is affine then so is
`X`. This file proves it over the terminal scheme; the general base is read over the terminal
scheme in `AlgebraicGeometry.Space.C1573.isAffineSpace_of_isThickening`.

The argument is the one of Stacks 07VU/07VT specialised to a thickening, run without the
integral-morphism machinery of Stacks 09YA. The space `X` is quasi-compact and quasi-separated
because `G` is and `G ⟶ X` is a surjective closed immersion. By Stacks 07SU, in the form of a
presentation by a system of étale quotients `X = lim Xᵢ` with bounded charts, each `Xᵢ` has a
surjective étale chart by a Noetherian scheme, so the reduction `(Xᵢ)_red ⊂ Xᵢ` is a finite
order thickening (`AlgebraicGeometry.Space.isFiniteOrderThickening_of_atlas`), and so is its
inverse image `Zᵢ ⊂ X` (Stacks 09ZX). The `Zᵢ` decrease (a reduced space maps into the reduction,
Stacks 03JJ), their intersection `W` lies in `G` because its points over the limit chart
`V = lim Vᵢ` kill the nilpotent functions of every `Vᵢ`
(`AlgebraicGeometry.Space.le_of_isThickening_of_isLimit`), so `W` is a closed subspace of the
affine `G` and is affine. Stacks 07SQ
(`AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded`) applied to the system `(Zᵢ)`
makes some `Zᵢ` affine, and then `X`, a finite order thickening of `Zᵢ`, is affine by
`AlgebraicGeometry.Space.isAffineSpace_of_isFiniteOrderThickening`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isThickening_of_terminal`: the statement over the
  terminal scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

attribute [local instance] AlgebraicGeometry.Space.pointTopology

universe v w u

namespace AlgebraicGeometry.Space

section Lemmas

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A constant system has bounded charts as soon as its index category is small.** The base
change of an affine scheme-valued point along an identity is the point itself. -/
theorem chartsBounded_const {I : Type u} [Category.{u} I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : ChartsBounded B S hS D) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    ChartsBounded B S hS ((Functor.const I).obj F) where
  mk_lt := h.mk_lt
  mk_over_lt := h.mk_over_lt
  bound i₀ U₀ f₀ := by
    have hstrong := B.cutoff_isStrongPrelimit
    set s := ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U₀)).size
    have hs : s < B.cutoff := ((BigAffineFppf.inclusion B S hS).obj U₀).left.property
    refine ⟨max ((2 : Cardinal) ^ (2 : Cardinal) ^ s) s, max_lt (hstrong (hstrong hs)) hs, ?_⟩
    intro j a W e
    have : IsIso (pullback.snd (((Functor.const I).obj F).map a) f₀) := by
      show IsIso (pullback.snd (𝟙 F) f₀)
      infer_instance
    let e' : yoneda.obj W ≅ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
      e ≪≫ asIso (pullback.snd (((Functor.const I).obj F).map a) f₀)
    let m := (BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimageIso e').hom
    calc ((BigFppfOver.toScheme B S hS).obj W).size ≤ max (2 ^ #((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj U₀))) s := Scheme.size_le_of_mono m
      _ ≤ max ((2 : Cardinal) ^ (2 : Cardinal) ^ s) s := max_le_max
          (power_le_power_left two_ne_zero (Scheme.mk_le_two_pow_size _)) le_rfl

end Lemmas

/-! ### The intersection of a decreasing system of subfunctors is its limit -/

section Intersection

variable {C : Type w} [Category.{v} C] {F : C ⥤ Type u} {J : Type u} [Category.{u} J]
  [IsCofiltered J] (Z : J → Subfunctor F) (hZ : ∀ {i j : J} (_ : i ⟶ j), Z i ≤ Z j)

/-- The system of subfunctors of a decreasing family. -/
abbrev subfunctorSystem : J ⥤ C ⥤ Type u where
  obj j := (Z j).toFunctor
  map g := Subfunctor.homOfLe (hZ g)

/-- The cone over a decreasing family of subfunctors given by their intersection. -/
abbrev subfunctorIInfCone : Cone (subfunctorSystem Z hZ) where
  pt := (⨅ j, Z j).toFunctor
  π := { app j := Subfunctor.homOfLe (iInf_le Z j) }

/-- In a cone over a decreasing family of subfunctors indexed by a cofiltered category, all the
legs pick the same element of the ambient functor. -/
theorem val_π_app_eq (s : Cone (subfunctorSystem Z hZ)) (j k : J) (U : C) (x : s.pt.obj U) :
    ((s.π.app j).app U x).1 = ((s.π.app k).app U x).1 := by
  obtain ⟨m, a', b', -⟩ := IsCofilteredOrEmpty.cone_objs j k
  have h1 := ConcreteCategory.congr_hom (congr_app (s.w a') U) x
  have h2 := ConcreteCategory.congr_hom (congr_app (s.w b') U) x
  simp only [NatTrans.comp_app_apply] at h1 h2
  rw [← h1, ← h2]
  rfl

/-- The intersection of a cofiltered decreasing family of subfunctors is its limit. -/
def isLimitSubfunctorIInfCone : IsLimit (subfunctorIInfCone Z hZ) where
  lift s := Subfunctor.lift (s.π.app (IsCofiltered.nonempty (C := J)).some ≫
      (Z (IsCofiltered.nonempty (C := J)).some).ι) (by
    rintro U _ ⟨x, rfl⟩
    simp only [Subfunctor.iInf_obj, Set.mem_iInter]
    intro j
    change ((s.π.app _).app U x).1 ∈ _
    rw [← val_π_app_eq Z hZ s j]
    exact ((s.π.app j).app U x).2)
  fac s j := by
    rw [← cancel_mono (Z j).ι]
    dsimp only [subfunctorIInfCone, subfunctorSystem]
    rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.lift_ι]
    ext U x
    exact val_π_app_eq Z hZ s (IsCofiltered.nonempty (C := J)).some j U x
  uniq s m hm := by
    rw [← cancel_mono (⨅ j, Z j).ι, Subfunctor.lift_ι,
      ← hm (IsCofiltered.nonempty (C := J)).some]
    dsimp only [subfunctorIInfCone, subfunctorSystem]
    rw [Category.assoc, Subfunctor.homOfLe_ι]

end Intersection

/-! ### The statement over the terminal scheme -/

section Terminal

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

omit [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)] in
/-- The charts `Vⱼ` of a presentation by a system of étale quotients are Noetherian schemes:
they are quasi-compact and locally of finite type over `Spec ℤ`. -/
theorem QuotientApproximation.isNoetherian_obj {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (A : QuotientApproximation hZ X) (j : A.Iᵒᵖ) :
    _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (A.E.obj.obj j)) := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal |>.symm
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian e.hom
  have := A.hlft j
  have := A.hcpt j
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (A.E.obj.obj j)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (A.E.obj.obj j)))
  exact {}

/-- **A thickening of an affine algebraic space over the terminal scheme is affine.** -/
theorem isAffineSpace_of_isThickening_of_terminal {X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    {G : Subfunctor X.1} (hG : IsThickening B (⊤_ Scheme.{u}) hZ X G)
    (hGa : IsAffineSpace B (⊤_ Scheme.{u}) hZ G.toFunctor) :
    IsAffineSpace B (⊤_ Scheme.{u}) hZ X.1 := by
  classical
  -- `X` is quasi-compact and quasi-separated
  have hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X.1 :=
    isQuasiCompactSpace_of_isThickening B _ hZ hG hGa.isQuasiCompactSpace
  have hGqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ G.toFunctor := by
    let Gs : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨G.toFunctor, hG.1.1⟩
    let V : SpacesEtale B (⊤_ Scheme.{u}) hZ Gs := ⟨Over.mk (𝟙 Gs), fun U φ hφ ↦ hφ⟩
    exact isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ _
      (isQuasiCompactSeparated_of_isAffineSpace B (⊤_ Scheme.{u}) hZ hZ Gs V hGa).2
  have hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X.1 :=
    isAbsolutelyQuasiSeparated_of_isSurjective_of_universallyClosed B (⊤_ Scheme.{u}) hZ hZ hG.1.1
      X.2 G.ι hG.2
      (universallyClosed_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ hG.1.1 X.2 G.ι hG.1.2) hGqs
  -- Stacks 07SU: a presentation by a small system of étale quotients
  obtain ⟨A, hAsmall⟩ := (nonempty_quotientApproximation X.2 hqc hqs).some.exists_small
  let := A.preorder
  have := A.nonempty
  have := A.isDirected
  have : ∀ {i j : A.Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (A.E.obj.map g)) := fun g => A.hobj g
  obtain ⟨e, he⟩ := A.exists_iso_limit X.2.isSheaf
  let Q := A.E.quotient
  let hQ : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (Q.obj j) := fun j =>
    A.E.isAlgebraicSpace_quotient_obj j
  let π : ∀ j, X.1 ⟶ Q.obj j := fun j => e.hom ≫ limit.π Q j
  have hπw : ∀ {i j : A.Iᵒᵖ} (g : i ⟶ j), π i ≫ Q.map g = π j := fun {i j} g => by
    show (e.hom ≫ limit.π Q i) ≫ Q.map g = e.hom ≫ limit.π Q j
    rw [Category.assoc, limit.w]
  have hfπ : ∀ j, A.f ≫ π j = yoneda.map (A.cV.π.app j) ≫ A.E.toQuotient.app j := fun j => by
    show A.f ≫ e.hom ≫ limit.π Q j = _
    rw [← Category.assoc, he, EtaleRelationSystem.limitToQuotient_π]
  -- the reductions of the stages, and their inverse images
  let R : ∀ j, Subfunctor (Q.obj j) := fun j =>
    reducedClosedSubspace B (⊤_ Scheme.{u}) hZ (Q.obj j) (hQ j) Set.univ isClosed_univ
  have hRc : ∀ j, IsClosedSubspace B (⊤_ Scheme.{u}) hZ (R j) := fun j =>
    isClosedSubspace_reducedClosedSubspace B (⊤_ Scheme.{u}) hZ (Q.obj j) (hQ j) Set.univ
      isClosed_univ
  have hRpts : ∀ j, Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (R j).toFunctor (R j).ι) =
      Set.univ := fun j =>
    range_pointsMap_ι_reducedClosedSubspace B (⊤_ Scheme.{u}) hZ (Q.obj j) (hQ j) Set.univ
      isClosed_univ
  have hRred : ∀ j, HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ (R j).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) := fun j =>
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B (⊤_ Scheme.{u}) hZ (Q.obj j) (hQ j)
      Set.univ isClosed_univ
  have hRthick : ∀ j, IsThickening B (⊤_ Scheme.{u}) hZ ⟨Q.obj j, hQ j⟩ (R j) := fun j =>
    ⟨hRc j, fun x => Set.eq_univ_iff_forall.1 (hRpts j) x⟩
  have hRfin : ∀ j, IsFiniteOrderThickening B (⊤_ Scheme.{u}) hZ ⟨Q.obj j, hQ j⟩ (R j) :=
      fun j => by
    have := A.isNoetherian_obj j
    exact isFiniteOrderThickening_of_atlas B (⊤_ Scheme.{u}) hZ (hRthick j) (A.E.obj.obj j)
      (A.E.toQuotient.app j)
      (quotientMap_surjective_unconditional B _ hZ (A.E.s.app j) (A.E.t.app j))
      (quotientMap_etale_unconditional B _ hZ (A.E.s.app j) (A.E.t.app j))
  let Z : A.Iᵒᵖ → Subfunctor X.1 := fun j => (R j).preimage (π j)
  have hZfin : ∀ j, IsFiniteOrderThickening B (⊤_ Scheme.{u}) hZ X (Z j) := fun j =>
    isFiniteOrderThickening_preimage B (⊤_ Scheme.{u}) hZ (R j)
      (ObjectProperty.homMk (π j) : X ⟶ ⟨Q.obj j, hQ j⟩) (hRfin j)
  have hZthick : ∀ j, IsThickening B (⊤_ Scheme.{u}) hZ X (Z j) := fun j => (hZfin j).choose_spec.1
  -- the inverse images decrease
  have hZm : ∀ {i j : A.Iᵒᵖ} (_ : i ⟶ j), Z i ≤ Z j := by
    intro i j g
    obtain ⟨h, hh⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B (⊤_ Scheme.{u}) hZ
      (hQ j) (hRc i).1 (R j) (hRc j) (hRred i) ((R i).ι ≫ Q.map g)).2 (by
        rw [hRpts j]
        exact Set.subset_univ _)
    intro U x hx
    show (π j).app U x ∈ (R j).obj U
    rw [← hπw g]
    have h2 : (Q.map g).app U ((π i).app U x) = (h.app U ⟨(π i).app U x, hx⟩).1 :=
      (ConcreteCategory.congr_hom (congr_app hh U) ⟨(π i).app U x, hx⟩).symm
    show (Q.map g).app U ((π i).app U x) ∈ (R j).obj U
    rw [h2]
    exact (h.app U _).2
  -- the intersection `W` of the `Zⱼ` lies in `G`, hence is affine
  let W : Subfunctor X.1 := ⨅ j, Z j
  have hWc : IsClosedSubspace B (⊤_ Scheme.{u}) hZ W :=
    isClosedSubspace_sInf B (⊤_ Scheme.{u}) hZ X.2 _ (by rintro _ ⟨j, rfl⟩; exact (hZthick j).1)
  have hWG : W ≤ G := by
    refine le_of_isThickening_of_isLimit hG W A.E.obj A.cV A.hV A.f A.hsurj A.hetale ?_
    intro T v hv j U _ t ht
    have hvZ : (π j).app (op T) (A.f.app (op T) v) ∈ (R j).obj (op T) :=
      (iInf_le Z j : W ≤ Z j) (op T) hv
    have e1 : (π j).app (op T) (A.f.app (op T) v) =
        (A.E.toQuotient.app j).app (op T) (v ≫ A.cV.π.app j) :=
      ConcreteCategory.congr_hom (congr_app (hfπ j) (op T)) v
    rw [e1] at hvZ
    have hqE : IsEtale B (⊤_ Scheme.{u}) hZ (A.E.toQuotient.app j) :=
      (isEtale_iff_presheaf_of_yoneda B _ hZ _).2
        (quotientMap_etale_unconditional B _ hZ (A.E.s.app j) (A.E.t.app j))
    have hVj := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ (A.E.obj.obj j)
    have hPc : IsClosedSubspace B (⊤_ Scheme.{u}) hZ ((R j).preimage (A.E.toQuotient.app j)) :=
      isClosedSubspace_preimage B _ hZ (A.E.toQuotient.app j) (R j) (hQ j) hVj (hRc j)
    have hPred : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ
        ((R j).preimage (A.E.toQuotient.app j)).toFunctor (fun Y : Scheme.{u} => IsReduced Y) := by
      have heq := preimage_reducedClosedSubspace_of_isSmooth B (⊤_ Scheme.{u}) hZ (hQ j) hVj
        (A.E.toQuotient.app j) (isSmooth_of_isEtale B _ hZ (hQ j) hqE) Set.univ isClosed_univ
      show HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ
        ((reducedClosedSubspace B (⊤_ Scheme.{u}) hZ (Q.obj j) (hQ j) Set.univ
          isClosed_univ).preimage (A.E.toQuotient.app j)).toFunctor _
      rw [heq]
      exact hasEtaleLocalProperty_isReduced_reducedClosedSubspace B _ hZ _ hVj _ _
    exact app_eq_zero_of_mem_of_hasEtaleLocalProperty_isReduced B (⊤_ Scheme.{u}) hZ
      ((R j).preimage (A.E.toQuotient.app j)) hPc hPred (v ≫ A.cV.π.app j) hvZ U t ht
  have hWa : IsAffineSpace B (⊤_ Scheme.{u}) hZ W.toFunctor :=
    isAffineSpace_of_isAffineHom_of_algebraicSpaces (W := ⟨W.toFunctor, hWc.1⟩)
      (X := ⟨G.toFunctor, hG.1.1⟩)
      (ObjectProperty.homMk (Subfunctor.homOfLe hWG)) (isAffineHom_of_isClosedImmersion B _ hZ _
        (isClosedImmersion_homOfLe' B _ hZ hWc.2 hWG)) hGa
  -- the descent situation of the `Zⱼ`, with bounded charts
  let D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ A.I :=
    { system := subfunctorSystem Z hZm
      algebraicSpace := fun i => (hZthick (op i)).1.1
      transition_affine := fun g => isAffineHom_of_isClosedImmersion B _ hZ _
        (isClosedImmersion_homOfLe' B _ hZ (hZthick _).1.2 (hZm g))
      quasiCompact := fun i => (isQuasiCompactSpace_iff_of_isHomeomorph_pointsMap B _ hZ
        (IsThickening.inclusion B _ hZ (hZthick (op i)))
        (isHomeomorph_pointsMap_ι_of_isThickening B _ hZ (hZthick (op i)))).2 hqc
      quasiSeparated := fun i => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ
        (hZthick (op i)).1.1 hqs (isQuasiSeparated_of_isClosedImmersion B _ hZ (hZthick (op i)).1.2)
      limitCone := subfunctorIInfCone Z hZm
      isLimit := isLimitSubfunctorIInfCone Z hZm
      limitAlgebraicSpace := hWc.1
      base := Classical.arbitrary A.I }
  let η : subfunctorSystem Z hZm ⟶ (Functor.const A.Iᵒᵖ).obj X.1 :=
    { app := fun j => (Z j).ι
      naturality := fun i j g => by
        dsimp only [subfunctorSystem, Functor.const_obj_map]
        rw [Subfunctor.homOfLe_ι]
        exact (Category.comp_id _).symm }
  have hb : ChartsBounded B (⊤_ Scheme.{u}) hZ D.system :=
    ChartsBounded.of_mono (chartsBounded_const (A.chartsBounded_of_small hAsmall) X.1) η
      (fun j => presheaf_monomorphisms_of_le
        (fun _ _ f (hf : _root_.AlgebraicGeometry.IsClosedImmersion f) => (inferInstance : Mono f))
        (hZthick j).1.2)
      (fun _ => isAffineHom_id X.1)
  obtain ⟨j, -, hj⟩ := hasAffineStageDescent_of_chartsBounded B (⊤_ Scheme.{u}) hZ hZ D hb hWa
  exact isAffineSpace_of_isFiniteOrderThickening B _ hZ (hZfin (op j)) hj

end Terminal

end AlgebraicGeometry.Space

end
