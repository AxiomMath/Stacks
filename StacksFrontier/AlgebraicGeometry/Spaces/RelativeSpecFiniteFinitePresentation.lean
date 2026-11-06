module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPointsSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The relative spectrum of a finite algebra of finite presentation

Let `X` be an algebraic space over a scheme `S` of a big fppf site and `𝒜` a quasi-coherent sheaf
of `𝒪_X`-algebras which is finite and of finite presentation, in the chartwise sense of
`AlgebraicGeometry.Space.AlgebraSheaf.IsFinite` and
`AlgebraicGeometry.Space.AlgebraSheaf.IsFinitePresentation`.  This file shows that the relative
spectrum `\underline{Spec}_X(𝒜)` of Stacks 081W, in the form of its functor of points
`AlgebraicGeometry.Space.relativeSpecPoints 𝒜`, is an algebraic space whose projection to `X` is
finite (Stacks 03ZP) and of finite presentation (Stacks 03XP, part (3)).  This is the input the
proof of Stacks 0GUM asks of the relative spectra `X_i = \underline{Spec}_Y(𝒜_i)`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBelowCutoff_of_isFinite`: a finite sheaf of
  `𝒪_X`-algebras has fewer than `B.cutoff` sections over every étale chart, which is the size
  condition under which the relative spectrum is constructed.
* `AlgebraicGeometry.Space.presheaf_relativeSpecPointsπ_of_affineChart`: a property of morphisms of
  schemes which is stable under base change, Zariski local and fppf local on the target, and holds
  for `Spec 𝒜(V) ⟶ V` at every affine étale chart `V`, holds for every represented base change of
  the projection of the relative spectrum.
* `AlgebraicGeometry.Space.isAlgebraicSpace_isFinite_isFinitePresentation_relativeSpecPointsπ`:
  the main statement.

## Implementation notes

**The size bound.**  Over an affine chart `W` the ring `𝒜(W)` is a finite module over `Γ(W)`,
hence has at most `max ℵ₀ #Γ(W)` elements.  Over an arbitrary chart `V` the sections inject, by
the sheaf property, into the product of the sections over the affine opens of `chartScheme V`;
with `s = size(chartScheme V)` each factor has at most `2 ^ s` elements and there are at most `s`
factors, so `#𝒜(V) ≤ (2 ^ s) ^ s = 2 ^ s`, which is below the cutoff because the cutoff is a
strong limit.

**Finiteness and finite presentation.**  The projection `π` of the relative spectrum is
representable and affine (`isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints`).
Over an affine open `V` of a surjective étale atlas `U ⟶ X` its fibre is `Spec 𝒜(V) ⟶ V`
(`isPullback_affineChartSpec`), which is finite and of finite presentation by hypothesis.  These
fibres glue over `U` (`exists_representing_over_of_openCover_of_size_le`) to a scheme over `U`
with the same property, the property being Zariski local on the target, and the property then
descends along the atlas (`presheaf_of_surjectiveEtaleChart_of_descent`), being fppf local on the
target.  Quasi-compactness and quasi-separatedness of `π` follow from its affineness.

No hypothesis is placed on `X`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The size bound for a finite algebra -/

/-- A finite ring map does not raise the cardinality beyond `max ℵ₀`: the target is a quotient of
a finite power of the source. -/
theorem _root_.RingHom.Finite.mk_le {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (hf : f.Finite) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) : #A ≤ κ := by
  let := f.toAlgebra
  have : Module.Finite R A := hf
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R A
  calc #A ≤ #(Fin n → R) := mk_le_of_surjective hg
    _ = #R ^ n := by simp
    _ ≤ κ ^ n := power_le_power_right hR
    _ ≤ κ := power_nat_le hκ

variable {B S hS} in
/-- **A finite sheaf of `𝒪_X`-algebras has fewer than `B.cutoff` sections over every étale
chart.**  See the implementation notes. -/
theorem AlgebraSheaf.sectionsBelowCutoff_of_isFinite {X : AlgebraicSpaces B S hS}
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (hAfin : A.IsFinite) :
    AlgebraSheaf.SectionsBelowCutoff B S hS A := by
  intro V
  set s := (chartScheme V).size
  have hs0 : ℵ₀ ≤ s := Scheme.aleph0_le_size _
  have hscut : s < B.cutoff := V.obj.left.left.property
  -- the bound over the affine opens of the chart
  have hO : ∀ O : (chartScheme V).affineOpens,
      #(A.right.obj.obj (op (openChart B S hS X.1 V O.1))) ≤ 2 ^ s := by
    intro O
    exact RingHom.Finite.mk_le (hAfin _ (isAffine_chartScheme_openChart B S hS X.1 V O))
      (hs0.trans (cantor s).le)
      ((Scheme.mk_sections_le_two_pow_size _ ⊤).trans
        (power_le_power_left two_ne_zero (Scheme.size_coe_opens_le (chartScheme V) O.1)))
  -- the sections over the chart inject into the product of those over its affine opens
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (A.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ A.right.property)
  let ρ : A.right.obj.obj (op V) →
      ∀ O : (chartScheme V).affineOpens, A.right.obj.obj (op (openChart B S hS X.1 V O.1)) :=
    fun x O => (A.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}).map
      (openChartInclusion B S hS X.1 V O.1).op x
  have hρ : Function.Injective ρ := by
    intro x y hxy
    refine (hsheaf _
      (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X.1 V)).isSeparatedFor.ext ?_
    rintro Z f ⟨_, h, _, ⟨O⟩, rfl⟩
    have := congrFun hxy O.down
    simp only [ρ] at this
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, this]
  calc #(A.right.obj.obj (op V))
      ≤ #(∀ O : (chartScheme V).affineOpens,
          A.right.obj.obj (op (openChart B S hS X.1 V O.1))) := mk_le_of_injective hρ
    _ = Cardinal.prod fun O : (chartScheme V).affineOpens =>
          #(A.right.obj.obj (op (openChart B S hS X.1 V O.1))) := mk_pi _
    _ ≤ Cardinal.prod fun _ : (chartScheme V).affineOpens => (2 ^ s : Cardinal.{u}) :=
          prod_le_prod _ _ hO
    _ = (2 ^ s) ^ #(chartScheme V).affineOpens := prod_const' _ _
    _ ≤ (2 ^ s) ^ s := power_le_power_left (power_ne_zero _ two_ne_zero)
          (Scheme.mk_affineOpens_le_size _)
    _ = 2 ^ s := by rw [← power_mul, mul_eq_self hs0]
    _ < B.cutoff := B.cutoff_isStrongPrelimit hscut

/-! ### The spectrum over an affine chart -/

section AffineChart

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (V : SmallEtale B S hS X.1) [IsAffine (chartScheme V)]

/-- Over an affine chart of a finite algebra, `Spec 𝒜(V) ⟶ V` is finite. -/
theorem isFinite_specChartMap (hAfin : A.IsFinite) :
    _root_.AlgebraicGeometry.IsFinite (specChartMap B S hS A V) := by
  have : _root_.AlgebraicGeometry.IsFinite (Spec.map (chartAlgebraMap B S hS A V)) :=
    (IsFinite.SpecMap_iff _).2 (hAfin V ‹IsAffine (chartScheme V)›)
  unfold specChartMap
  infer_instance

/-- Over an affine chart of an algebra of finite presentation, `Spec 𝒜(V) ⟶ V` is locally of
finite presentation. -/
theorem locallyOfFinitePresentation_specChartMap (hAfp : A.IsFinitePresentation) :
    LocallyOfFinitePresentation (specChartMap B S hS A V) := by
  have : LocallyOfFinitePresentation (Spec.map (chartAlgebraMap B S hS A V)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (hAfp V ‹IsAffine (chartScheme V)›)
  unfold specChartMap
  infer_instance

end AffineChart

/-! ### Properties of the projection which are local on the target -/

section Projection

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_relativeSpecFiniteFinitePresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_relativeSpecFiniteFinitePresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A) (hAq : A.IsQuasicoherent)

include hA hAq in
/-- **A property local on the target which holds over every affine chart holds for the projection
of the relative spectrum.**  Let `Q` be a property of morphisms of schemes, stable under base
change, Zariski local on the target and descending along surjective flat morphisms locally of
finite presentation.  If `Spec 𝒜(V) ⟶ V` has `Q` for every affine étale chart `V` of `X`, then
every represented base change of `π : \underline{Spec}_X(𝒜) ⟶ X` has `Q`. -/
theorem presheaf_relativeSpecPointsπ_of_affineChart (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] (hQ : IsZariskiLocalAtTarget Q)
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hQV : ∀ (V : SmallEtale B S hS X.1) [IsAffine (chartScheme V)],
      Q (specChartMap B S hS A V)) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (relativeSpecPointsπ B S hS A) := by
  have hRI : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsAffineHom.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hF := isSheaf_relativeSpecPoints B S hS A
  obtain ⟨-, hπ⟩ :=
    isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints B S hS A hA hF hAq
  set π := relativeSpecPointsπ B S hS A
  obtain ⟨U, a, hs, he⟩ := X.2.exists_atlas
  let Uc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, he⟩
  obtain ⟨V', hV'⟩ := AlgebraSheaf.exists_dominatingChart B S hS A Uc
  -- the affine opens of the atlas, as objects of the site and as étale charts of `X`
  choose V u hu hurange hVaff using
    fun O => BigFppfOver.exists_affineOpen_restrict B S hS U O
  have hu' : ∀ O, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (u O)) :=
    hu
  let Vc : ∀ O, SmallEtale B S hS X.1 := fun O =>
    etaleChartOfIsEtale B S hS (yoneda.map (u O) ≫ Uc.obj.hom)
      (isEtale_yoneda_map_comp_of_isOpenImmersion B S hS Uc (u O))
  have hVcaff : ∀ O, IsAffine (chartScheme (Vc O)) := hVaff
  -- over each of them the fibre of `π` is `Spec 𝒜(V)`
  have hpb : ∀ O, IsPullback (affineChartSpecToPoints B S hS A hA (Vc O)
      (exists_chartEval_eq B S hS A hAq (Vc O)))
      (yoneda.map (affineChartSpecHom B S hS A hA (Vc O))) π (yoneda.map (u O) ≫ a) :=
    fun O => isPullback_affineChartSpec B S hS A hA (Vc O)
      (injective_chartEval_of_isAffine B S hS A hAq (Vc O))
      (exists_chartEval_eq B S hS A hAq (Vc O))
  have hpbU : IsPullback (pullback.fst π a) (pullback.snd π a) π a := IsPullback.of_hasPullback π a
  have hpb' : ∀ O, IsPullback (hpbU.lift (affineChartSpecToPoints B S hS A hA (Vc O)
      (exists_chartEval_eq B S hS A hAq (Vc O)))
      (yoneda.map (affineChartSpecHom B S hS A hA (Vc O)) ≫ yoneda.map (u O))
      (by rw [(hpb O).w, Category.assoc])) (yoneda.map (affineChartSpecHom B S hS A hA (Vc O)))
      (pullback.snd π a) (yoneda.map (u O)) := fun O => IsPullback.of_right' (hpb O) hpbU
  have hQp : ∀ O, Q ((BigFppfOver.toScheme B S hS).map (affineChartSpecHom B S hS A hA (Vc O))) :=
    fun O => by
      rw [toScheme_map_affineChartSpecHom]
      exact hQV (Vc O)
  -- the uniform size bound
  have hsize : ∀ O, ((BigFppfOver.toScheme B S hS).obj
      (affineChartSpec B S hS A hA (Vc O))).size ≤ max ℵ₀ #(A.right.obj.obj (op V')) := by
    intro O
    have := hu' O
    show (Spec (A.right.obj.obj (op (Vc O)))).size ≤ _
    rw [Scheme.size_Spec]
    refine max_le_max le_rfl ?_
    let W : (chartScheme Uc).affineOpens :=
      ⟨((BigFppfOver.toScheme B S hS).map (u O)).opensRange,
        isAffineOpen_opensRange ((BigFppfOver.toScheme B S hS).map (u O))⟩
    obtain ⟨k, hk⟩ := hV' W
    have e := etaleChartIsoChartOpensOfIsOpenImmersion B S hS Uc (u O)
    calc #(A.right.obj.obj (op (Vc O)))
        = #(A.right.obj.obj (op ((chartOpens B S hS Uc).obj
            ((BigFppfOver.toScheme B S hS).map (u O)).opensRange))) :=
          mk_congr ((CategoryTheory.forget CommRingCat).mapIso
            (A.right.obj.mapIso e.op)).toEquiv.symm
      _ ≤ #(A.right.obj.obj (op V')) := mk_le_of_surjective hk
  -- the fibre over the atlas is a scheme with `Q` over it
  obtain ⟨Y₀, e, P, hP, hQP⟩ := exists_representing_over_of_openCover_of_size_le B S hS hQ
    (BigFppfOver.isSheaf_pullback_yoneda_obj π a hF X.2.isSheaf) (pullback.snd π a)
    hu (fun y => by
      have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hy
      obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨O, by rwa [hurange O]⟩)
    hpb' hQp (max_lt B.aleph0_lt_cutoff (hA V')) hsize
  have hVQ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd π a) := by
    rw [show pullback.snd π a = e.hom ≫ yoneda.map P by rw [← hP, Iso.hom_inv_id_assoc]]
    exact MorphismProperty.RespectsIso.precomp _ e.hom _
      ((presheaf_yoneda_map_iff B S hS inferInstance P).2 hQP)
  have hVP : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd π a) :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hpbU hπ
  exact presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hF X.2.isSheaf hs he hVP hVQ

end Projection

/-- A property of morphisms of schemes which holds for affine morphisms holds for every
`IsAffineHom` presheaf morphism. -/
private theorem presheaf_of_isAffineHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf f)
    {P : MorphismProperty Scheme.{u}}
    (h : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y) [_root_.AlgebraicGeometry.IsAffineHom g], P g) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_monotone
    (fun _ _ _q (_hq : _root_.AlgebraicGeometry.IsAffineHom _) => h _) _ hf

/-! ### The main statement -/

/-- **The relative spectrum of a finite quasi-coherent algebra of finite presentation is an
algebraic space, finite and of finite presentation over the base.**

Let `X` be an algebraic space over `S` and `𝒜` a quasi-coherent sheaf of `𝒪_X`-algebras whose
structure map is finite and of finite presentation on every affine étale chart.  Then the functor
of points of `\underline{Spec}_X(𝒜)` (Stacks 081W) is an algebraic space, and its projection to
`X` is finite in the sense of Stacks 03ZP and of finite presentation in the sense of
Stacks 03XP, part (3).  No hypothesis is placed on `X`. -/
theorem isAlgebraicSpace_isFinite_isFinitePresentation_relativeSpecPointsπ
    {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hAq : A.IsQuasicoherent) (hAfin : A.IsFinite) (hAfp : A.IsFinitePresentation) :
    IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A) ∧
      IsFinite B S hS (relativeSpecPointsπ B S hS A) ∧
      IsFinitePresentation B S hS (relativeSpecPointsπ B S hS A) := by
  have hA := AlgebraSheaf.sectionsBelowCutoff_of_isFinite hAfin
  obtain ⟨hP, hπ⟩ := isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints B S hS A hA
    (isSheaf_relativeSpecPoints B S hS A) hAq
  have _hfd := isFinite_descendsAlong_fppf.{u}
  have hfin : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (relativeSpecPointsπ B S hS A) :=
    presheaf_relativeSpecPointsπ_of_affineChart B S hS A hA hAq _ isZariskiLocalAtTarget_isFinite
      fun V _ => isFinite_specChartMap B S hS A V hAfin
  have hlfploc : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FinitePresentation)
  have _hlfpd := descendsAlong_fppf_of (@LocallyOfFinitePresentation.{u})
  have hlfp : (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (relativeSpecPointsπ B S hS A) :=
    presheaf_relativeSpecPointsπ_of_affineChart B S hS A hA hAq _ hlfploc
      fun V _ => locallyOfFinitePresentation_specChartMap B S hS A V hAfp
  refine ⟨hP, isFinite_of_presheaf_isFinite B S hS _ hfin, ?_, ?_, ?_⟩
  · exact presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS _
      (fun i p hi hp => by
        have : Etale i := hi
        have : LocallyOfFinitePresentation p := hp
        infer_instance) _ hlfp
  · exact isQuasiCompact_of_presheaf B S hS _
      (presheaf_of_isAffineHom B S hS hπ (P := @QuasiCompact) fun _ _ => inferInstance)
  · exact isQuasiSeparated_of_isSeparated B S hS
      ((isSeparated_iff_presheaf B S hS _ hP X.2 hπ.rep).2
        (presheaf_of_isAffineHom B S hS hπ (P := @_root_.AlgebraicGeometry.IsSeparated)
          fun _ _ => inferInstance))

end AlgebraicGeometry.Space

end
