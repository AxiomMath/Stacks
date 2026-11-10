module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.Coords
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.Classes
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.UnitTuple

/-!
# The Abel morphism over a chart on which a section basis exists

Let `X` be a smooth proper geometrically irreducible curve over a field `k`, `H` the Hilbert scheme
of degree-`d` divisors, `B₀` a `k`-scheme with an invertible module `L₀` on `X_{B₀}` of degree `d`
on every fibre, and `e₀, …, e_m` sections of `L₀` forming a basis after every affine base change
into an open `V ⊆ B₀` (`Stacks.RigidifiedPicard.IsSectionBasis`). For `v : T ⟶ B₀` into `V` and
functions `c₀, …, c_m` on `T` spanning the unit ideal, the zero scheme of `∑ cᵢ eᵢ` is a degree-`d`
Hilbert family `Stacks.RigidifiedPicard.abelFamily`, classified by
`Stacks.RigidifiedPicard.famHom : T ⟶ H`. This morphism

* is natural in `T` (`Stacks.RigidifiedPicard.comp_famHom`);
* depends only on the point `[c₀ : … : c_m]` of `ℙᵐ` (`Stacks.RigidifiedPicard.famHom_congr`), and,
  over an affine `T`, determines it (`Stacks.RigidifiedPicard.homOfCoords_eq_of_famHom_eq`);
* reaches, over an affine `T`, every morphism `T ⟶ H` whose family has the class of the pullback
  of `L₀` (`Stacks.RigidifiedPicard.exists_famHom_eq`);
* lies over `v` through the Abel morphism when `L₀` is the translated universal class
  (`Stacks.RigidifiedPicard.famHom_comp_abelMorphism`).

These are the chartwise statements from which the Abel morphism is identified with a projective
space bundle in the proof of [Stacks, Tag 0BA0] (5).

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

open Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {n : ℕ} (es : Fin n → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  [LocallyOfFiniteType f] (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  {d : ℕ}
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)

/-- Functions spanning the unit ideal have no common zero. -/
theorem forall_exists_mem_basicOpen_of_span_eq_top {T : Scheme.{u}} (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (t : T) : ∃ i, t ∈ T.basicOpen (c i) := by
  by_contra ht
  push Not at ht
  have hmem : ∀ i, T.presheaf.germ ⊤ t trivial (c i) ∈
      IsLocalRing.maximalIdeal (T.presheaf.stalk t) := fun i => by
    by_contra hi
    exact ht i ((T.mem_basicOpen_top (c i) t).2
      ((IsLocalRing.mem_maximalIdeal _).not.1 hi |> not_not.1))
  have h1 : (1 : Γ(T, ⊤)) ∈ Ideal.span (Set.range c) := hc ▸ Submodule.mem_top
  have h2 := Ideal.mem_map_of_mem (T.presheaf.germ ⊤ t trivial).hom h1
  rw [Ideal.map_span, map_one] at h2
  refine (IsLocalRing.maximalIdeal.isMaximal (T.presheaf.stalk t)).ne_top
    ((Ideal.eq_top_iff_one _).2 ?_)
  refine Ideal.span_le.2 ?_ h2
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hmem i

include hbasis hdeg₀ in
/-- **The degree-`d` Hilbert family `Z(∑ cᵢ eᵢ)`** over `T` mapping into `V`, for functions
spanning the unit ideal. -/
noncomputable def abelFamily {T : Over (Spec (.of k))} (v : T ⟶ B₀) (hv : Set.range v.left ⊆ V)
    (c : Fin n → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    Stacks.Hilbert.HilbertFamily (Over.mk f) T d where
  ideal :=
    haveI : SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
      (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mp hL₀
    Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ es v c)
  isFiniteLocallyFreeOfRank := by
    have : SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
      (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mp hL₀
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    have : SmoothOfRelativeDimension 1 (bcProj f T) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback f T.hom) inferInstance
    have hM : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2
        ((Scheme.Modules.pullback (bcMap f v)).obj L₀) :=
      Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f v).toLRSHom.toShHom L₀ hL₀
    have hdimT : ∀ t : T.left, topologicalKrullDim ↥((bcProj f T).fiber t) ≤ 1 :=
      topologicalKrullDim_fiber_bcProj_le f hdim T
    refine (isFiniteLocallyFreeOfRank_zeroScheme_of_ne_zero (bcProj f T)
      (isIntegral_curveFibre f T) hdimT ((Scheme.Modules.pullback (bcMap f v)).obj L₀) hM _
      (pullbackGlobalSections_fiberι_abelSection_ne_zero f L₀ es hbasis v hv c
        (forall_exists_mem_basicOpen_of_span_eq_top c hc)) d fun t => ?_).2
    have hcl : Stacks.SheafOfModules.picardClass (bc f T).presheaf
        (Stacks.RingedSpace.structureIsSheaf (bc f T).toRingedSpace)
        ((Scheme.Modules.pullback (bcMap f v)).obj L₀) hM =
        schemePullbackClass (bcMap f v) (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
          (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) :=
      (pullbackClass_classOf (bcMap f v).toLRSHom.toShHom L₀ hL₀).symm
    rw [hcl, relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback
      (bcMap_isPullback_proj f v) (topologicalKrullDim_fiber_bcProj_le f hdim B₀) hdimT t]
    exact hdeg₀ _

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {n : ℕ} (es : Fin n → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  [LocallyOfFiniteType f] (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  {d : ℕ}
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)

/-- An invertible module in the presheaf sense is invertible for the sheaf of rings. -/
private theorem isInvertible_sheaf_of_isInvertible {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
    (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀) :
    SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hL₀

/-- **The class of `Z(∑ cᵢ eᵢ)` is the pullback of the class of `L₀`.** -/
theorem abelClass_abelFamily {T : Over (Spec (.of k))} (v : T ⟶ B₀) (hv : Set.range v.left ⊆ V)
    (c : Fin n → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    abelClass f (abelFamily f L₀ hL₀ es hbasis hdim hdeg₀ v hv c hc) =
      schemePullbackClass (bcMap f v) (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
        (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) := by
  have := isInvertible_sheaf_of_isInvertible f L₀ hL₀
  have hM : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2
      ((Scheme.Modules.pullback (bcMap f v)).obj L₀) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f v).toLRSHom.toShHom L₀ hL₀
  have : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme (bc f T) _
      (abelSection f L₀ es v c)) :=
    (abelFamily f L₀ hL₀ es hbasis hdim hdeg₀ v hv c hc).isRelativeEffectiveCartierDivisor.1
  exact (picardClass_zeroScheme _ hM _).trans
    (pullbackClass_classOf (bcMap f v).toLRSHom.toShHom L₀ hL₀).symm

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {m : ℕ} (es : Fin (m + 1) → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  [LocallyOfFiniteType f] (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  {d : ℕ}
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)
  {H : Over (Spec (.of k))} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

/-- **The morphism to the Hilbert scheme classifying `Z(∑ cᵢ eᵢ)`.** -/
noncomputable def famHom {T : Over (Spec (.of k))} (v : T ⟶ B₀) (hv : Set.range v.left ⊆ V)
    (c : Fin (m + 1) → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) : T ⟶ H :=
  hH.family.symm (abelFamily f L₀ hL₀ es hbasis hdim hdeg₀ v hv c hc)

/-- **Naturality of `famHom`.** -/
theorem comp_famHom {T T' : Over (Spec (.of k))} (a : T' ⟶ T) (v : T ⟶ B₀)
    (hv : Set.range v.left ⊆ V) (c : Fin (m + 1) → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (hv' : Set.range (a ≫ v).left ⊆ V) :
    a ≫ famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c hc =
      famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (a ≫ v) hv' (fun i => a.left.appTop (c i))
        (span_range_appTop_comp a.left c hc) := by
  refine hH.family.injective ?_
  rw [family_comp f hH a]
  simp only [famHom, Equiv.apply_symm_apply]
  refine Stacks.Hilbert.HilbertFamily.ext ?_
  rw [Stacks.Hilbert.baseChange_ideal, familyBaseChangeMap_eq]
  exact (zeroScheme_abelSection_comp f L₀ hL₀ es a v c).symm

/-- **`famHom` depends only on the point of projective space.** -/
theorem famHom_congr {T : Over (Spec (.of k))} (v : T ⟶ B₀) (hv : Set.range v.left ⊆ V)
    (c c' : Fin (m + 1) → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (hc' : Ideal.span (Set.range c') = ⊤) (h : homOfCoords c hc = homOfCoords c' hc') :
    famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c hc =
      famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c' hc' := by
  obtain ⟨u, hu⟩ := (homOfCoords_eq_iff c c' hc hc').1 h
  have := isInvertible_sheaf_of_isInvertible f L₀ hL₀
  refine congrArg hH.family.symm (Stacks.Hilbert.HilbertFamily.ext ?_)
  change Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ es v c) =
    Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ es v c')
  rw [show c' = fun i => (u : Γ(T.left, ⊤)) * c i from funext hu, abelSection_smul]
  exact (Stacks.Divisors.zeroScheme_smul_of_isUnit _ _ (u.isUnit.map _)).symm

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {m : ℕ} (es : Fin (m + 1) → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  [LocallyOfFiniteType f] (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  {d : ℕ}
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)
  {H : Over (Spec (.of k))} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

include hbasis in
/-- **Over an affine `T` mapping into `V`, a morphism to the Hilbert scheme whose family has the
class of the pullback of `L₀` is some `famHom`.** -/
theorem exists_famHom_eq {T : Over (Spec (.of k))} [IsAffine T.left] (v : T ⟶ B₀)
    (hv : Set.range v.left ⊆ V) (mT : T ⟶ H)
    (hcl : abelClass f (hH.family mT) = schemePullbackClass (bcMap f v)
      (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
        (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀)) :
    ∃ (c : Fin (m + 1) → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤),
      mT = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c hc := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  set Z := hH.family mT
  let D : (bc f T).IdealSheafData := Z.ideal
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := Z.isRelativeEffectiveCartierDivisor.1
  have hfib : ∀ t : T.left,
      Stacks.Divisors.IsEffectiveCartierDivisor (D.comap ((bcProj f T).fiberι t)) := fun t => by
    have hW := Z.isRelativeEffectiveCartierDivisor
    have : Flat (Z.ideal.subschemeι ≫ bcProj f T) := hW.2
    exact isEffectiveCartierDivisor_comap_of_isPullback (bcProj f T) (T.left.fromSpecResidueField t)
      (IsPullback.of_hasPullback (bcProj f T) (T.left.fromSpecResidueField t)).flip Z.ideal hW.1
  have hne : ∀ t : T.left, Nonempty ((bcProj f T).fiber t) := fun t =>
    have := isIntegral_curveFibre f T t
    inferInstance
  obtain ⟨c, hc, hZ⟩ := exists_abelSection_zeroScheme_eq f L₀ hL₀ es hbasis v hv D hfib hne hcl
  refine ⟨c, span_range_eq_top_of_forall_mem_basicOpen c hc, hH.family.injective ?_⟩
  simp only [famHom, Equiv.apply_symm_apply]
  exact Stacks.Hilbert.HilbertFamily.ext hZ.symm

include hbasis in
/-- **Over an affine `T`, two `famHom` agree only for proportional coefficients.** -/
theorem homOfCoords_eq_of_famHom_eq {T : Over (Spec (.of k))} [IsAffine T.left] (v : T ⟶ B₀)
    (hv : Set.range v.left ⊆ V) (c c' : Fin (m + 1) → Γ(T.left, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (hc' : Ideal.span (Set.range c') = ⊤)
    (h : famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c hc =
      famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c' hc') :
    homOfCoords c hc = homOfCoords c' hc' := by
  have h' := congrArg Stacks.Hilbert.HilbertFamily.ideal (congrArg hH.family h)
  simp only [famHom, Equiv.apply_symm_apply] at h'
  exact (homOfCoords_eq_iff c c' hc hc').2
    (exists_unit_of_zeroScheme_abelSection_eq f L₀ hL₀ es hbasis v hv c c'
      (forall_exists_mem_basicOpen_of_span_eq_top c hc)
      (forall_exists_mem_basicOpen_of_span_eq_top c' hc') h')

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {m : ℕ} (es : Fin (m + 1) → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  [LocallyOfFiniteType f] (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  {d : ℕ}
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)
  {H : Over (Spec (.of k))} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  (A : Grp (Over (Spec (.of k)))) (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X)
  (hθ : ∀ s : Spec (.of k), relativeInvertibleDegreeHomAt f hdim s θ = d)
  (ι₀ : B₀ ⟶ A.X)
  (hclass : Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀ =
    schemePullbackClass (bcMap f ι₀) (abelTranslatedClass f hdim σ hσ A eA θ))

include hclass in
/-- **`famHom` lies over `v` through the Abel morphism.** -/
theorem famHom_comp_abelMorphism {T : Over (Spec (.of k))} (v : T ⟶ B₀)
    (hv : Set.range v.left ⊆ V) (c : Fin (m + 1) → Γ(T.left, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c hc ≫
        abelMorphism f hdim σ hσ θ hθ hH A eA = v ≫ ι₀ := by
  refine family_symm_comp_abelMorphism_of_abelClass_eq f hdim σ hσ A eA θ hθ hH (v ≫ ι₀) _ ?_
  rw [abelClass_abelFamily, hclass, schemePullbackClass_comp, ← bcMap_comp]

end Stacks.RigidifiedPicard

end
