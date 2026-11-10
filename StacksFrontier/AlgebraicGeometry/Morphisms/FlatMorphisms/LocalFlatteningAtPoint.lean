module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Henselian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.LocalFlatteningCondition
public import StacksFrontier.RingTheory.Flat.HenselianFlatteningTheorem
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover

/-!
# The local flattening subscheme at a point

Let `S` be a scheme which is the spectrum of its henselian local ring at a point `s`, let
`f : X ⟶ S` be locally of finite type, `F` a quasi-coherent `𝒪_X`-module of finite type and
`x ∈ X` a point over `s`. Stacks 05PG, applied to the local flattening problem at `x`, gives an
ideal of `𝒪_{S,s}`; the closed subscheme of `S` it cuts out detects, after every pointed base
change `(T, t) ⟶ (S, s)`, flatness of `F_T` over `T` at the points of `X_T` above `t` and `x`:
that holds exactly when `Spec 𝒪_{T,t} ⟶ S` factors through it. When `f` is of finite
presentation at `x` and `F_x` is finitely presented, the closed subscheme is of finite
presentation. This is the scheme-theoretic reformulation recorded as Stacks 05PH.

## Main results

* `AlgebraicGeometry.LocalFlattening.exists_closedSubscheme_flatOverAt_iff_factorStalk`
* `LocalFlattening.exists_finitePresentation_closedSubscheme_flatOverAt_iff_factorStalk`

## Implementation notes

A henselian local scheme with closed point `s` is represented intrinsically, by the isomorphism
`Spec 𝒪_{S,s} ⟶ S` and henselianity of `𝒪_{S,s}`. A closed subscheme is represented by its ideal
sheaf.

## References

* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
* [Stacks Project, Tag 05PH](https://stacks.math.columbia.edu/tag/05PH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.LocalFlattening

open Opposite TopologicalSpace

private alias isIso_appTop_of_isIso := Stacks.AlgebraicGeometry.isIso_appTop_of_isIso

private def closedSubschemeOfStalkIdeal
    {S : Scheme.{u}} (s : S) (J : Ideal (S.presheaf.stalk s)) :
    S.IdealSheafData := by
  let α := S.fromSpecStalk s
  let γ := Scheme.ΓSpecIso (CommRingCat.of (S.presheaf.stalk s))
  let e : CommRingCat.of Γ(S, ⊤) ⟶ CommRingCat.of (S.presheaf.stalk s) :=
    α.appTop ≫ γ.hom
  exact Scheme.IdealSheafData.ofIdealTop (J.comap e.hom)

private lemma ideal_ofIdealTop_top {S : Scheme.{u}} [IsAffine S]
    (J : Ideal Γ(S, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal
      ⟨⊤, isAffineOpen_top S⟩ = J := by
  simp

private lemma closedSubschemeOfStalkIdeal_ideal_top {S : Scheme.{u}} (s : S) [IsAffine S]
    (J : Ideal (S.presheaf.stalk s)) :
    (closedSubschemeOfStalkIdeal s J).ideal ⟨⊤, isAffineOpen_top S⟩ =
      J.comap ((S.fromSpecStalk s).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (S.presheaf.stalk s))).hom).hom :=
  ideal_ofIdealTop_top _

private lemma exists_lift_iff_ideal_top_le {S : Scheme.{u}} [IsAffine S] (I : S.IdealSheafData)
    {R : Type u} [CommRing R] (q : Spec (.of R) ⟶ S) :
    (∃ h : Spec (.of R) ⟶ I.subscheme, h ≫ I.subschemeι = q) ↔
      I.ideal ⟨⊤, isAffineOpen_top S⟩ ≤ RingHom.ker q.appTop.hom := by
  constructor
  · rintro ⟨h, rfl⟩ b hb
    have hb' : I.subschemeι.appTop.hom b = 0 :=
      RingHom.mem_ker.mp (by
        change b ∈ RingHom.ker
          (I.subschemeι.app (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)).hom
        rwa [Scheme.IdealSheafData.ker_subschemeι_app])
    rw [RingHom.mem_ker, Scheme.Hom.comp_appTop]
    simp [CommRingCat.hom_comp, hb']
  · intro hle
    have hQ : I ≤ q.ker := by
      apply Scheme.IdealSheafData.le_of_isAffine
      have hQker : q.ker.ideal ⟨⊤, isAffineOpen_top S⟩ = RingHom.ker q.appTop.hom := by
        convert Scheme.Hom.ker_apply q ⟨⊤, isAffineOpen_top S⟩ using 1
        rfl
      rw [hQker]
      exact hle
    have hLift : I.subschemeι.ker ≤ q.ker := by rwa [I.ker_subschemeι]
    exact ⟨_, IsClosedImmersion.lift_fac I.subschemeι q hLift⟩

private theorem factor_through_stalk_ideal_subscheme_iff
    {S : Scheme.{u}} (s : S) [IsIso (S.fromSpecStalk s)]
    {R : Type u} [CommRing R] (J : Ideal (S.presheaf.stalk s))
    (φ : CommRingCat.of (S.presheaf.stalk s) ⟶ CommRingCat.of R)
    (q : Spec (.of R) ⟶ S)
    (hq : q = Spec.map φ ≫ S.fromSpecStalk s) :
    (∃ h : Spec (.of R) ⟶ (closedSubschemeOfStalkIdeal s J).subscheme,
      h ≫ (closedSubschemeOfStalkIdeal s J).subschemeι = q) ↔
      Ideal.map φ.hom J = ⊥ := by
  let α := S.fromSpecStalk s
  let γS := Scheme.ΓSpecIso (CommRingCat.of (S.presheaf.stalk s))
  let γR := Scheme.ΓSpecIso (CommRingCat.of R)
  let e : CommRingCat.of Γ(S, ⊤) ⟶ CommRingCat.of (S.presheaf.stalk s) :=
    α.appTop ≫ γS.hom
  let κ : CommRingCat.of Γ(S, ⊤) ⟶ CommRingCat.of R := q.appTop ≫ γR.hom
  have hκ : κ.hom = φ.hom.comp e.hom := by
    change (q.appTop ≫ γR.hom).hom = φ.hom.comp (α.appTop ≫ γS.hom).hom
    rw [hq, Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    simp only [CommRingCat.hom_comp]
    rfl
  have hκker : RingHom.ker κ.hom = RingHom.ker q.appTop.hom := by
    change RingHom.ker (γR.hom.hom.comp q.appTop.hom) = _
    exact RingHom.ker_equiv_comp q.appTop.hom γR.commRingCatIsoToRingEquiv
  let : IsAffine S := (IsAffine.iff_of_isIso α).mp inferInstance
  have heSurj : Function.Surjective e.hom := by
    have := isIso_appTop_of_isIso α
    exact ((ConcreteCategory.isIso_iff_bijective e).mp inferInstance).2
  rw [exists_lift_iff_ideal_top_le, closedSubschemeOfStalkIdeal_ideal_top,
    Ideal.map_eq_bot_iff_le_ker, ← hκker]
  constructor
  · intro hle a ha
    obtain ⟨b, rfl⟩ := heSurj a
    have hb : b ∈ RingHom.ker κ.hom := hle (show b ∈ J.comap e.hom from ha)
    rw [RingHom.mem_ker, hκ] at hb
    exact RingHom.mem_ker.mpr hb
  · intro hJ b hb
    rw [RingHom.mem_ker, hκ]
    exact RingHom.mem_ker.mp (hJ (show e.hom b ∈ J from hb))

private theorem exists_local_flattening_ideal
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] (x : X) (s : S) (hxs : f x = s)
    [HenselianLocalRing (S.presheaf.stalk s)] :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
      (pointedStalkMap f x s hxs).hom.toAlgebra
    ∃ I : Ideal (S.presheaf.stalk s),
      (∀ (R : LocalAlgCat.{u, u} (S.presheaf.stalk s)),
        (localFlatSituation f F x s hxs).Condition R ↔
          Ideal.map (algebraMap (S.presheaf.stalk s) R) I = ⊥) ∧
      ((algebraMap (localFlatSituation f F x s hxs).A
          (localFlatSituation f F x s hxs).B).EssentiallyOfFinitePresentation →
        Module.FinitePresentation (localFlatSituation f F x s hxs).B
          (localFlatSituation f F x s hxs).M → I.FG) := by
  let : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) :=
    (pointedStalkMap f x s hxs).hom.toAlgebra
  let L := localFlatSituation f F x s hxs
  have : Algebra.EssFiniteType L.A L.B := by
    change Algebra.EssFiniteType (S.presheaf.stalk s) (X.presheaf.stalk x)
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ (f.stalkMap x)).mpr
      (LocallyOfFiniteType.stalkMap f x)
  have : Module.Finite L.B L.M := finite_modulesStalk F x
  have : HenselianLocalRing L.A := ‹HenselianLocalRing (S.presheaf.stalk s)›
  exact L.exists_ideal_condition_iff_map_eq_bot_of_henselian.{u, u, u, u}

/-- The ideal of `𝒪_{S,s}` whose closed subscheme detects flatness after pointed base change. -/
private theorem exists_ideal_factorStalk_iff
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (s : S) (hxs : f x = s)
    [HenselianLocalRing (S.presheaf.stalk s)] [IsIso (S.fromSpecStalk s)] :
    ∃ J : Ideal (S.presheaf.stalk s),
      ((pointedStalkMap f x s hxs).hom.EssentiallyOfFinitePresentation →
        Module.FinitePresentation (X.presheaf.stalk x) (modulesStalk F x) → J.FG) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (_ht : g t = s),
        (∀ y : pullback (C := Scheme.{u}) f g,
            (pullback.snd f g y = t) →
            (pullback.fst f g y = x) →
              AlgebraicGeometry.IsFlatOverAt
                (pullback.snd f g).toLRSHom.toShHom
                ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y) ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ (closedSubschemeOfStalkIdeal s J).subscheme,
            h ≫ (closedSubschemeOfStalkIdeal s J).subschemeι = T.fromSpecStalk t ≫ g := by
  obtain ⟨J, hJ, hJfg⟩ := exists_local_flattening_ideal f F x s hxs
  refine ⟨J, hJfg, fun {T} g t ht => ?_⟩
  let φ : CommRingCat.of (S.presheaf.stalk s) ⟶ CommRingCat.of (T.presheaf.stalk t) :=
    eqToHom (congrArg S.presheaf.stalk ht).symm ≫ g.stalkMap t
  exact (condition_iff_forall_isFlatOverAt f g F x s t hxs ht).symm.trans
    ((hJ (pointedStalkLocalAlgebra g s t ht)).trans
      (factor_through_stalk_ideal_subscheme_iff s J φ
        (T.fromSpecStalk t ≫ g) (specMap_pointedStalkMap_fromSpecStalk g t s ht).symm).symm)

/-- **The local flattening subscheme at a point** (the scheme-theoretic reformulation of
Stacks 05PG recorded as Stacks 05PH). Over a scheme `S` which is the spectrum of its henselian
local ring at `s`, a closed subscheme of `S` detects, after every pointed base change
`(T, t) ⟶ (S, s)`, flatness over `T` of the pulled-back module at every point of `X_T` above
`t` and `x`: that holds exactly when `Spec 𝒪_{T,t} ⟶ S` factors through it. -/
public theorem exists_closedSubscheme_flatOverAt_iff_factorStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (s : S) (hxs : f x = s)
    [HenselianLocalRing (S.presheaf.stalk s)]
    [IsIso (S.fromSpecStalk s)] :
    ∃ I : S.IdealSheafData,
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (_ht : g t = s),
        (∀ y : pullback (C := Scheme.{u}) f g,
            (pullback.snd f g y = t) →
            (pullback.fst f g y = x) →
              AlgebraicGeometry.IsFlatOverAt
                (pullback.snd f g).toLRSHom.toShHom
                ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y) ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme,
            h ≫ I.subschemeι = T.fromSpecStalk t ≫ g := by
  obtain ⟨J, -, hJ⟩ := exists_ideal_factorStalk_iff f F x s hxs
  exact ⟨_, hJ⟩

private lemma essentiallyOfFinitePresentation_stalkMap_of_finitePresentationAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsIso (S.fromSpecStalk (f x))]
    (hfp : AlgebraicGeometry.FinitePresentationAt f x) :
    (f.stalkMap x).hom.EssentiallyOfFinitePresentation := by
  obtain ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, hUV, hfp⟩ := hfp
  -- every open containing the closed point `f x` of the local scheme `S` is all of `S`
  have hVtop : V = ⊤ := by
    have hs : f x ∈ V := hUV hx
    have hpre : S.fromSpecStalk (f x) ⁻¹ᵁ V = ⊤ :=
      Scheme.preimage_eq_top_of_closedPoint_mem _
        (by simpa only [Scheme.fromSpecStalk_closedPoint] using hs)
    apply top_unique
    intro z _
    obtain ⟨w, rfl⟩ := (S.fromSpecStalk (f x)).surjective z
    change w ∈ S.fromSpecStalk (f x) ⁻¹ᵁ V
    rw [hpre]
    trivial
  subst V
  let a := S.presheaf.germ ⊤ (f x) trivial
  -- the germ at `f x` of the global sections is invertible, `S` being the spectrum of its stalk
  have : IsIso a := by
    have := isIso_appTop_of_isIso (S.fromSpecStalk (f x))
    have he : a = (S.fromSpecStalk (f x)).appTop ≫
        (Scheme.ΓSpecIso (S.presheaf.stalk (f x))).hom := by
      rw [Scheme.fromSpecStalk_appTop]
      simp [a]
    rw [he]
    infer_instance
  let b := f.appLE ⊤ U hUV
  let c := X.presheaf.germ U x hx
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let D := Γ(X, U)
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : Algebra A D := (inv a ≫ b).hom.toAlgebra
  let : Algebra D B := c.hom.toAlgebra
  have hcomp : a ≫ f.stalkMap x = b ≫ c := by
    dsimp [a, b, c]
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]
    exact Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have htower : f.stalkMap x = (inv a ≫ b) ≫ c := by
    rw [Category.assoc, ← hcomp]
    simp
  have : IsScalarTower A D B :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom htower)
  have hfp' : (inv a ≫ b).hom.FinitePresentation :=
    RingHom.FinitePresentation.comp hfp
      (RingHom.FinitePresentation.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (inv a)).mp inferInstance))
  have : Algebra.FinitePresentation A D := hfp'
  have : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl B :=
    hU.isLocalization_stalk ⟨x, hx⟩
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl, inferInstance⟩

private lemma finitePresentation_closedSubschemeOfStalkIdeal
    {S : Scheme.{u}} (s : S) [IsIso (S.fromSpecStalk s)]
    (J : Ideal (S.presheaf.stalk s)) (hJ : J.FG) :
    AlgebraicGeometry.FinitePresentation (closedSubschemeOfStalkIdeal s J).subschemeι := by
  let : IsAffine S := (IsAffine.iff_of_isIso (S.fromSpecStalk s)).mp inferInstance
  let I := closedSubschemeOfStalkIdeal s J
  let e := (S.fromSpecStalk s).appTop ≫ (Scheme.ΓSpecIso (S.presheaf.stalk s)).hom
  have := isIso_appTop_of_isIso (S.fromSpecStalk s)
  let E := (asIso e).commRingCatIsoToRingEquiv
  have hK : (J.comap e.hom).FG := by
    change (J.comap E.toRingHom).FG
    simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_coe, Ideal.comap_coe,
      Ideal.map_symm] using
      (hJ.map E.symm.toRingHom)
  have hker : (RingHom.ker I.subschemeι.appTop.hom).FG := by
    change (RingHom.ker (I.subschemeι.app (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)).hom).FG
    rwa [Scheme.IdealSheafData.ker_subschemeι_app, closedSubschemeOfStalkIdeal_ideal_top]
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have : LocallyOfFinitePresentation I.subschemeι :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.FinitePresentation.of_surjective _
        (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top S⟩) hker)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **The local flattening subscheme at a point, finite presentation.** If `f` is of finite
presentation at `x` and the stalk `F_x` is a finitely presented `𝒪_{X,x}`-module, the closed
subscheme of `exists_closedSubscheme_flatOverAt_iff_factorStalk` may be chosen of finite
presentation over `S`. -/
public theorem exists_finitePresentation_closedSubscheme_flatOverAt_iff_factorStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (s : S) (hxs : f x = s)
    [HenselianLocalRing (S.presheaf.stalk s)]
    [IsIso (S.fromSpecStalk s)]
    (hfp : AlgebraicGeometry.FinitePresentationAt f x)
    (hFfp : Module.FinitePresentation (X.presheaf.stalk x) (modulesStalk F x)) :
    ∃ I : S.IdealSheafData,
      AlgebraicGeometry.FinitePresentation I.subschemeι ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (_ht : g t = s),
        (∀ y : pullback (C := Scheme.{u}) f g,
            (pullback.snd f g y = t) →
            (pullback.fst f g y = x) →
              AlgebraicGeometry.IsFlatOverAt
                (pullback.snd f g).toLRSHom.toShHom
                ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y) ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme,
            h ≫ I.subschemeι = T.fromSpecStalk t ≫ g := by
  subst s
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (pointedStalkMap f x (f x) rfl).hom.toAlgebra
  let L := localFlatSituation f F x (f x) rfl
  have hB : (algebraMap L.A L.B).EssentiallyOfFinitePresentation := by
    change ((pointedStalkMap f x (f x) rfl).hom).EssentiallyOfFinitePresentation
    simp only [pointedStalkMap, eqToHom_refl, Category.id_comp]
    exact essentiallyOfFinitePresentation_stalkMap_of_finitePresentationAt f x hfp
  obtain ⟨J, hJfg, hJ⟩ := exists_ideal_factorStalk_iff f F x (f x) rfl
  exact ⟨_, finitePresentation_closedSubschemeOfStalkIdeal (f x) J (hJfg hB hFfp), hJ⟩

end AlgebraicGeometry.LocalFlattening
