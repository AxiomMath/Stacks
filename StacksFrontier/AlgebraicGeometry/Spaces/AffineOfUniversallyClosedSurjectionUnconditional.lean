module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionsCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraSmallFiniteSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPointsColimit

/-!
# A surjective universally closed morphism with affine source has affine target (Stacks 07VT)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, surjective and universally
closed, with `X` affine.  Then `Y` is affine.  On the way, the relative spectrum of a directed
colimit of `𝒪_Y`-algebras is shown to be the limit, in presheaves, of the relative spectra.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpecPointsMap` and
  `AlgebraicGeometry.Space.relativeSpecPointsFunctor`: the functoriality of the relative spectrum
  `AlgebraicGeometry.Space.relativeSpecPoints` in the algebra.

## Main results

* `AlgebraicGeometry.Space.nonempty_isLimit_relativeSpecPointsFunctor_mapCone`: the relative
  spectrum of a directed colimit of algebras is the limit, in presheaves, of the relative spectra.
* `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`:
  a surjective universally closed morphism of algebraic spaces with affine source has affine
  target.

## References

* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of the relative spectrum in the algebra -/

section RelativeSpecFunctor

variable {X : AlgebraicSpaces B S hS}

/-- Restricting a point of a relative spectrum along an algebra morphism commutes with base
change of the point along `g : T' ⟶ T`. -/
theorem RelativeSpecPoint.comap_map {A A' : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A' ⟶ A)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (p : RelativeSpecPoint B S hS A T) :
    (p.map B S hS g).comap φ = (p.comap φ).map B S hS g := by
  obtain ⟨x, α⟩ := p
  rw [RelativeSpecPoint.map_mk, RelativeSpecPoint.comap_mk, RelativeSpecPoint.comap_mk,
    RelativeSpecPoint.map_mk, compPushforwardAlgebraMap_def, compPushforwardAlgebraMap_def,
    Category.assoc]

/-- Under `relativeSpecPointsEquiv`, `relativeSpecPointsMap φ` is restriction of points along
`φ`. -/
theorem relativeSpecPointsEquiv_relativeSpecPointsMap {A A' : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (φ : A' ⟶ A) (T : BigFppfOver B S hS) (p : (relativeSpecPoints B S hS A).obj (op T)) :
    relativeSpecPointsEquiv B S hS A' T ((relativeSpecPointsMap B S hS φ).app (op T) p) =
      (relativeSpecPointsEquiv B S hS A T p).comap φ :=
  Equiv.apply_symm_apply _ _

/-- `relativeSpecPointsMap φ` commutes with the structure morphisms to `X`. -/
@[reassoc (attr := simp)]
theorem relativeSpecPointsMap_π {A A' : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A' ⟶ A) :
    relativeSpecPointsMap B S hS φ ≫ relativeSpecPointsπ B S hS A' =
      relativeSpecPointsπ B S hS A := by
  ext T p
  exact congrArg RelativeSpecPoint.pt
    (relativeSpecPointsEquiv_relativeSpecPointsMap B S hS φ T.unop p)

end RelativeSpecFunctor

/-! ### The relative spectrum turns a directed colimit of algebras into a limit -/

section Limit

variable {X : AlgebraicSpaces B S hS}

/-- A point of a relative spectrum is determined by its morphism transported to any point `x`
equal to its underlying point. -/
theorem RelativeSpecPoint.eq_mk_compPushforwardAlgebraMap {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A T) {x : X.1.obj (op T)}
    (h : x = p.pt) :
    p = ⟨x, compPushforwardAlgebraMap B S hS p.hom (specPointOverEq B S hS h)⟩ := by
  obtain ⟨y, α⟩ := p
  have e := RelativeSpecPoint.mk_comp_eq B S hS α h.symm (𝟙 _) (specPointOverEq B S hS h) rfl
  rwa [compPushforwardAlgebraMap_id] at e

/-- Equal points of a relative spectrum have equal morphisms once transported to a common
underlying point `x`. -/
theorem RelativeSpecPoint.compPushforwardAlgebraMap_congr {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} {x : X.1.obj (op T)} {q p : RelativeSpecPoint B S hS A T}
    (heq : q = p) (hq : x = q.pt) (hp : x = p.pt) :
    compPushforwardAlgebraMap B S hS q.hom (specPointOverEq B S hS hq) =
      compPushforwardAlgebraMap B S hS p.hom (specPointOverEq B S hS hp) := by
  subst heq
  rfl

/-- If `p'` is the restriction of `p` along `φ`, then `φ` followed by the morphism of `p`
transported to `x` is the morphism of `p'` transported to `x`. -/
theorem RelativeSpecPoint.comp_compPushforwardAlgebraMap_of_comap_eq
    {A A' : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A' ⟶ A) {T : BigFppfOver B S hS}
    {x : X.1.obj (op T)} (p : RelativeSpecPoint B S hS A T) (p' : RelativeSpecPoint B S hS A' T)
    (hp : p.comap φ = p') (hx : x = p.pt) (hx' : x = p'.pt) :
    φ ≫ compPushforwardAlgebraMap B S hS p.hom (specPointOverEq B S hS hx) =
      compPushforwardAlgebraMap B S hS p'.hom (specPointOverEq B S hS hx') := by
  subst hp
  rw [← compPushforwardAlgebraMap_comp_left]
  rfl

variable {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2}

/-- Transporting a morphism along `rfl : x = x` does nothing. -/
theorem compPushforwardAlgebraMap_pointOverEq_rfl {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} {x : X.1.obj (op T)}
    (f : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) :
    compPushforwardAlgebraMap B S hS f (specPointOverEq B S hS (rfl : x = x)) = f := by
  rw [show specPointOverEq B S hS (rfl : x = x) = 𝟙 _ from rfl, compPushforwardAlgebraMap_id]

omit [IsDirected J (· ≤ ·)] [Nonempty J] in
/-- A compatible family of morphisms out of the stages of a colimit has exactly one extension. -/
theorem existsUnique_comp_eq_of_isColimit {c : Cocone Φ} (hc : IsColimit c)
    {W : AlgebraSheaf.{u, u} B S hS X.1 X.2} (α : ∀ j, Φ.obj j ⟶ W)
    (hα : ∀ {i j : J} (f : i ⟶ j), Φ.map f ≫ α j = α i) :
    ∃! β : c.pt ⟶ W, ∀ j, c.ι.app j ≫ β = α j :=
  let cc : Cocone Φ := ⟨W, { app := α, naturality := fun i j f => by simpa using hα f }⟩
  ⟨hc.desc cc, fun j => hc.fac cc j, fun β hβ => hc.uniq cc β hβ⟩

/-- **A compatible family of points of the relative spectra of a directed system of algebras
comes from exactly one point of the relative spectrum of the colimit.** -/
theorem RelativeSpecPoint.existsUnique_comap_eq (c : Cocone Φ) (hc : IsColimit c)
    {T : BigFppfOver B S hS} (p : ∀ j : J, RelativeSpecPoint B S hS (Φ.obj j) T)
    (hp : ∀ {i j : J} (h : i ≤ j), (p j).comap (Φ.map (homOfLE h)) = p i) :
    ∃! q : RelativeSpecPoint B S hS c.pt T, ∀ j, q.comap (c.ι.app j) = p j := by
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  obtain ⟨x, hx⟩ : ∃ x, x = (p j₀).pt := ⟨_, rfl⟩
  have hpt : ∀ j, x = (p j).pt := fun j => by
    obtain ⟨k, hk₀, hk⟩ := exists_ge_ge j₀ j
    rw [hx, ← hp hk₀, ← hp hk]
    rfl
  obtain ⟨β, hβ, hβu⟩ := existsUnique_comp_eq_of_isColimit B S hS hc
    (W := pushforwardAlgebra B S hS (specPointOver B S hS T x))
    (fun j => compPushforwardAlgebraMap B S hS (p j).hom (specPointOverEq B S hS (hpt j)))
    fun {i j} f => by
      rw [show f = homOfLE (leOfHom f) from Subsingleton.elim _ _]
      exact RelativeSpecPoint.comp_compPushforwardAlgebraMap_of_comap_eq B S hS _ _ _
        (hp (leOfHom f)) (hpt j) (hpt i)
  refine ⟨⟨x, β⟩, fun j => ?_, fun q hq => ?_⟩
  · refine (RelativeSpecPoint.comap_mk _ x _).trans ?_
    refine (congrArg (RelativeSpecPoint.mk (A := Φ.obj j) x) (hβ j)).trans ?_
    exact ((p j).eq_mk_compPushforwardAlgebraMap B S hS (hpt j)).symm
  · obtain ⟨y, α'⟩ := q
    have hqpt : x = y := hx.trans (congrArg RelativeSpecPoint.pt (hq j₀)).symm
    subst hqpt
    refine congrArg (RelativeSpecPoint.mk (A := c.pt) x) ?_
    exact hβu α' fun j =>
      (compPushforwardAlgebraMap_pointOverEq_rfl B S hS (c.ι.app j ≫ α')).symm.trans
        (RelativeSpecPoint.compPushforwardAlgebraMap_congr B S hS (hq j) rfl (hpt j))

/-- **The relative spectrum of a directed colimit of algebras is the limit of the relative
spectra**, computed in presheaves. -/
theorem nonempty_isLimit_relativeSpecPointsFunctor_mapCone (c : Cocone Φ) (hc : IsColimit c) :
    Nonempty (IsLimit ((relativeSpecPointsFunctor B S hS X).mapCone c.op)) := by
  refine ⟨evaluationJointlyReflectsLimits _ fun T => Nonempty.some ?_⟩
  refine (Types.isLimit_iff _).mpr fun s hs => ?_
  obtain ⟨q, hq, huniq⟩ := RelativeSpecPoint.existsUnique_comap_eq B S hS c hc
    (T := T.unop) (fun j => relativeSpecPointsEquiv B S hS _ T.unop (s (op j))) fun {i j} h =>
      (relativeSpecPointsEquiv_relativeSpecPointsMap B S hS (Φ.map (homOfLE h)) T.unop
        (s (op j))).symm.trans (congrArg (relativeSpecPointsEquiv B S hS _ T.unop)
          (hs (homOfLE h).op))
  have hq' := Equiv.apply_symm_apply (relativeSpecPointsEquiv B S hS c.pt T.unop) q
  refine ⟨(relativeSpecPointsEquiv B S hS c.pt T.unop).symm q, fun j => ?_, fun y hy => ?_⟩
  · apply (relativeSpecPointsEquiv B S hS _ T.unop).injective
    exact (relativeSpecPointsEquiv_relativeSpecPointsMap B S hS (c.ι.app j.unop) T.unop _).trans
      ((congrArg (RelativeSpecPoint.comap (c.ι.app j.unop)) hq').trans (hq j.unop))
  · apply (relativeSpecPointsEquiv B S hS c.pt T.unop).injective
    exact (huniq _ fun j =>
      (relativeSpecPointsEquiv_relativeSpecPointsMap B S hS (c.ι.app j) T.unop y).symm.trans
        (congrArg (relativeSpecPointsEquiv B S hS _ T.unop) (hy (op j)))).trans hq'.symm

end Limit

/-! ### Stacks 07VT -/

section Main

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 07VT.** Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Assume that `X` is affine and that `f` is surjective and universally closed. Then `Y` is
affine. -/
@[stacks 07VT "target of a universally closed surjection from an affine algebraic space is affine"]
theorem isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (hclosed : UniversallyClosed B S hS f)
    (haff : IsAffineSpace B S hS X) :
    IsAffineSpace B S hS Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let V : SpacesEtale B S hS Xs := ⟨Over.mk (𝟙 Xs), fun U φ hφ ↦ hφ⟩
  have hXqcsep := isQuasiCompactSeparated_of_isAffineSpace B S hS hZ Xs V haff
  have hYqc : IsQuasiCompactSpace B S hS Y :=
    IsQuasiCompactSpace.of_isSurjective B S hS hX hY hsurj hXqcsep.1
  have hYsep : IsAbsolutelySeparated B S hS hZ Y :=
    isAbsolutelySeparated_of_isSurjective_of_universallyClosed B S hS hZ hX hY f hsurj hclosed
      hXqcsep.2
  have hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y :=
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ Y hYsep
  have haffHom : IsAffineHom B S hS f := by
    obtain ⟨T, hT, ⟨e⟩⟩ := haff
    simpa using isAffineHom_iso_comp e.hom
      (isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨T, hT⟩ (e.inv ≫ f) hYsep)
  have hint : IsIntegralHom B S hS f :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX hY f).2 ⟨haffHom, hclosed⟩
  let Zo : Over Ys := Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := Xs)
    (Y := Ys) f)
  have hZo : IsAffineHom B S hS Zo.hom.hom := haffHom
  let Za : AffineOver B S hS Ys := ⟨Zo, hZo⟩
  let A : AlgebraSheaf.{u, u} B S hS Ys.1 Ys.2 := pushforwardAlgebra B S hS Zo
  have hAqc : A.IsQuasicoherent :=
    ((quasicoherentPushforwardAlgebraFunctor B S hS Ys).obj (op Za)).property
  have hAint : A.IsIntegral := isIntegral_pushforwardAlgebra_over_of_isIntegralHom B S hS Zo
    (relativelyRepresentable_hom_of_isAffineHom B S hS Zo.hom hZo) hint
  have hAbd : AlgebraSheaf.SectionsBelowCutoff B S hS A :=
    sectionsBelowCutoff_pushforwardAlgebra B S hS Zo
  obtain ⟨U, q, hU, hqs', hqe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).mp hYqc
  let U₀ : SmallEtale B S hS Ys.1 := ⟨CostructuredArrow.mk q, presheaf_etale_of_isEtale B S hS hqe⟩
  have hU₀ : IsAffine (chartScheme U₀) := hU
  have hsurj₀ : IsSurjective B S hS U₀.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY U q).1 hqs'
  have := FiniteTypeSubalgebraIndex.isDirected (U₀ := U₀) hAqc
  have := FiniteTypeSubalgebraIndex.nonempty (U₀ := U₀) hAqc
  let Φ := FiniteTypeSubalgebraIndex.diagram (A := A) hU₀ hsurj₀
  let c := FiniteTypeSubalgebraIndex.cocone (A := A) hU₀ hsurj₀
  obtain ⟨hc⟩ := FiniteTypeSubalgebraIndex.nonempty_isColimit_cocone hU₀ hsurj₀ hYqc hYqs hAqc
  have hstageQc : ∀ j, (Φ.obj j).IsQuasicoherent := fun j => j.stage.property.1
  have hstageFinite : ∀ j, (Φ.obj j).IsFinite := fun j =>
    (isFinite_subobject_iff_isFiniteType' B S hS Ys.1 Ys.2 A hAint j.stage.obj).2
      j.stage.property.2
  have hstageAS : ∀ j, IsAlgebraicSpace B S hS (relativeSpecPoints B S hS (Φ.obj j)) := fun j =>
    (finiteTypeRelativeSpec B S hS ⟨Φ.obj j, hstageQc j⟩
      (hstageFinite j).isFiniteType).obj.left.property
  have hstageFin : ∀ j, IsFinite B S hS (relativeSpecPointsπ B S hS (Φ.obj j)) := fun j =>
    isFinite_finiteTypeRelativeSpec B S hS ⟨Φ.obj j, hstageQc j⟩ (hstageFinite j)
  have hstageSep : ∀ j, IsSeparated B S hS (relativeSpecPointsπ B S hS (Φ.obj j)) := fun j =>
    isSeparated_of_isFinite B S hS _ (hstageAS j) hY (hstageFin j)
  let D := Φ.op ⋙ relativeSpecPointsFunctor B S hS _
  have htrFin : ∀ {i j : (FiniteTypeSubalgebraIndex A U₀)ᵒᵖ} (g : i ⟶ j),
      IsFinite B S hS (D.map g) := by
    intro i j g
    refine isFinite_of_comp_of_isSeparated B S hS (D.map g) _ ?_ (hstageSep j.unop)
    rw [show D.map g ≫ relativeSpecPointsπ B S hS (Φ.obj j.unop) =
      relativeSpecPointsπ B S hS (Φ.obj i.unop) from relativeSpecPointsMap_π B S hS _]
    exact hstageFin i.unop
  obtain ⟨hlim⟩ := nonempty_isLimit_relativeSpecPointsFunctor_mapCone B S hS c hc
  obtain ⟨e⟩ := nonempty_iso_boundedRelativeSpec B S hS ⟨A, hAqc⟩ hAbd Za (Iso.refl _)
  let eX : X ≅ relativeSpecPoints B S hS A :=
    (ObjectProperty.ι _ ⋙ Over.forget Ys ⋙ ObjectProperty.ι _).mapIso e
  have heX : eX.hom ≫ relativeSpecPointsπ B S hS A = f :=
    congrArg (fun t => t.hom) (Over.w e.hom.hom)
  have hlimAS : IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A) :=
    IsAlgebraicSpace.of_iso hX eX
  have haffL : IsAffineSpace B S hS (relativeSpecPoints B S hS A) := haff.of_iso eX
  let E : DescentSituation B S hS hZ (FiniteTypeSubalgebraIndex A U₀) :=
    { system := D
      algebraicSpace := hstageAS
      transition_affine := fun g => (htrFin g).isAffineHom
      quasiCompact := fun j => isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc
        (isQuasiCompact_of_isAffineHom' B S hS _ (hstageAS j) hY (hstageFin j).isAffineHom)
      quasiSeparated := fun j => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
        (hstageAS j) hYqs (isQuasiSeparated_of_isSeparated B S hS (hstageSep j))
      limitCone := (relativeSpecPointsFunctor B S hS _).mapCone c.op
      isLimit := hlim
      limitAlgebraicSpace := hlimAS
      base := Classical.arbitrary _ }
  have hJ : Cardinal.mk (FiniteTypeSubalgebraIndex A U₀) < B.cutoff :=
    FiniteTypeSubalgebraIndex.mk_le.trans_lt (B.cutoff_isStrongPrelimit (hAbd U₀))
  have hle : (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) ≤
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) := fun _ _ g hg => by
    have : _root_.AlgebraicGeometry.IsFinite g := hg
    infer_instance
  have htr : ∀ {i j : (FiniteTypeSubalgebraIndex A U₀)ᵒᵖ} (g : i ⟶ j),
      (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (E.system.map g) := fun g =>
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hle) _
      ((isFinite_iff_representable B S hS (D.map g) (hstageAS _) (hstageAS _)).1 (htrFin g)).2
  obtain ⟨j, -, hjaff⟩ :=
    E.exists_isAffineSpace_system_obj_of_locallyOfFiniteType B S hS hZ hJ htr haffL
  have hsurjj : IsSurjective B S hS (relativeSpecPointsπ B S hS (Φ.obj j)) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨pointsMap B S hS X (eX.hom ≫ relativeSpecPointsMap B S hS (c.ι.app j)) x, ?_⟩
    rwa [← Function.comp_apply (f := pointsMap B S hS _ (relativeSpecPointsπ B S hS (Φ.obj j))),
      ← pointsMap_comp, Category.assoc, relativeSpecPointsMap_π B S hS (A := A) (c.ι.app j), heX]
  exact isAffineSpace_target_of_isFinite_of_isSurjective B S hS _ (hstageAS j) hY hsurjj
    (hstageFin j) hjaff

end Main

end AlgebraicGeometry.Space

end
