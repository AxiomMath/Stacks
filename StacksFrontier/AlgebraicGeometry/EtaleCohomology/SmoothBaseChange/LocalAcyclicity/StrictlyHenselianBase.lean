module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AnnihilatedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.StrictHenselizationCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.StrictHenselizationCohomologyIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.ConstantRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection

/-!
# Local acyclicity of a smooth morphism over its own strict henselization

Let `f : X ⟶ S` be a smooth morphism and `x` a geometric point of `X` such that the structure
morphism of the strict henselization of `S` at `f(x)` is an isomorphism. Then `f` is locally
acyclic at `x` relative to the constant sheaf `ℤ/nℤ`, for `n` invertible on `S`.

## Main results

* `isLocallyAcyclicAt_of_smooth_of_isIso_strictHenselizationToBase`: a smooth morphism over a
  base equal to its own strict henselization is locally acyclic for `ℤ/nℤ` with `n` invertible.

## References

* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
* [Stacks Project, Tag 0EZU](https://stacks.math.columbia.edu/tag/0EZU)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u})

/-- Sections of the constant sheaf with value `ℤ/nℤ` are annihilated by `n`. -/
theorem zsmul_constantSheaf_zmod_eq_zero (T : Scheme.{u}) (n : ℕ) (U : T.Etale)
    (a : ((constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).obj.obj (op U)) :
    (n : ℤ) • a = 0 := by
  have hA : (n : ℤ) • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) = 0 := by
    ext ⟨b⟩
    simp
  refine (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ (n : ℤ)).1 ?_ (op U) a
  rw [← (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).map_id, ← Functor.map_zsmul, hA,
    Functor.map_zero]

/-- **Derived sections of a sheaf in degree zero have no cohomology in negative degrees.** -/
theorem isZero_homology_smallEtaleDerivedGlobalSections_of_neg {T : Scheme.{u}}
    (L : smallEtaleDerivedCategory T) [L.IsGE 0] {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((smallEtaleDerivedGlobalSections T).obj L)) := by
  have : ((smallEtaleDerivedGlobalSections T).obj L).IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
      L 0
  exact DerivedCategory.isZero_of_isGE _ 0 q hq

variable {B}

/-- Restriction of derived sections from `Spec 𝒪^{sh}_{S,f(x)}` to `Spec 𝒪^{sh}_{X,x}` is
invertible. -/
private theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_strictHenselizationSquareMap_app
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (x : GeometricPoint X)
    (N : smallEtaleDerivedCategory (strictHenselization B S hS (x.map f))) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (strictHenselizationSquareMap B hX hS f x)).app N) := by
  let x₀ := geometricPointToStrictHenselization B X hX x
  let σ := strictHenselizationSquareMap B hX hS f x
  change IsIso ((smallEtaleDerivedGlobalSectionsRestriction σ).app N)
  have hcomp : x₀ ≫ σ = geometricPointToStrictHenselization B S hS (x.map f) :=
    geometricPointToStrictHenselization_strictHenselizationSquareMap B hX hS f x
  have hs₀ : (x₀ ≫ σ) (default : x.source) =
      IsLocalRing.closedPoint ↥(etaleLocalRing B S hS (x.map f)) := by
    rw [hcomp]
    exact geometricPointToStrictHenselization_base_default B S hS (x.map f)
  have := isIso_smallEtaleDerivedGlobalSectionsRestriction_of_strictlyHenselian (x₀ ≫ σ) hs₀ N
  have := isIso_smallEtaleDerivedGlobalSectionsRestriction_of_strictlyHenselian x₀
    (geometricPointToStrictHenselization_base_default B X hX x)
    ((smallEtaleDerivedPullbackAb σ).obj N)
  exact isIso_smallEtaleDerivedGlobalSectionsRestriction_app_of_comp x₀ σ N

/-- Restriction of constant coefficients along `c = a ≫ b` is invertible exactly when restriction
along `a` is, given that restriction along `b` is. -/
private theorem isIso_restriction_constantComplex_comp_iff {X₀ X₁ X₂ : Scheme.{u}} {a : X₀ ⟶ X₁}
    {b : X₁ ⟶ X₂} {c : X₀ ⟶ X₂} (h : a ≫ b = c) (M : Ab.{u + 1})
    [IsIso ((smallEtaleDerivedGlobalSectionsRestriction b).app
      (smallEtaleConstantComplexAb X₂ M))] :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction c).app (smallEtaleConstantComplexAb X₂ M)) ↔
      IsIso ((smallEtaleDerivedGlobalSectionsRestriction a).app
        (smallEtaleConstantComplexAb X₁ M)) :=
  h ▸ isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_constantComplex_iff a b M

/-- Over a base equal to its own strict henselization, restriction of constant coefficients
along `Spec 𝒪^{sh}_{X,x} ×_S Spec Ω ⟶ Spec Ω` is invertible when the base change maps of `f`
along `g : Spec Ω ⟶ S` are. -/
private theorem
    isIso_smallEtaleDerivedGlobalSectionsRestriction_pullback_snd_of_isIso_higherBaseChangeMapAb
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (x : GeometricPoint X)
    [IsIso (strictHenselizationToBase B S hS (x.map f))] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (g : Spec (.of Ω) ⟶ S) [QuasiCompact g] [QuasiSeparated g] (A : Ab.{u + 1}) [Finite A]
    (hbc : ∀ q : ℕ, IsIso ((higherBaseChangeMapAb f g (pullback.fst f g) (pullback.snd f g)
      pullback.condition q).app ((constantSheaf (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).obj
        A))) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (pullback.snd (strictHenselizationToBase B X hX x ≫ f) g)).app
        (smallEtaleConstantComplexAb (Spec (.of Ω)) A)) := by
  let π := strictHenselizationToBase B S hS (x.map f)
  let p := strictHenselizationToBase B X hX x
  let P := pullback π g
  let Q := pullback (p ≫ f) g
  let m : Q ⟶ P := strictHenselizationBaseChangeMap B hX hS f g x
  change IsIso ((smallEtaleDerivedGlobalSectionsRestriction (pullback.snd (p ≫ f) g)).app
    (smallEtaleConstantComplexAb (Spec (.of Ω)) A))
  have hcP : (smallEtaleConstantComplexAb P A).IsGE 0 := by
    change ((DerivedCategory.singleFunctor _ 0).obj _).IsGE 0
    infer_instance
  have hm' : IsIso ((smallEtaleDerivedGlobalSectionsRestriction m).app
      (smallEtaleConstantComplexAb P A)) := by
    rw [DerivedCategory.isIso_iff]
    intro q
    rcases lt_or_ge q 0 with hq | hq
    · have : ((smallEtaleDerivedPullbackAb m).obj (smallEtaleConstantComplexAb P A)).IsGE 0 :=
        (smallEtalePullbackAb m).isGE_obj_mapDerivedCategory _ 0 inferInstance
      exact ⟨⟨(isZero_homology_smallEtaleDerivedGlobalSections_of_neg _ hq).to_ _,
        (isZero_homology_smallEtaleDerivedGlobalSections_of_neg _ hq).eq_of_src _ _,
        (isZero_homology_smallEtaleDerivedGlobalSections_of_neg _ hq).eq_of_src _ _⟩⟩
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      obtain ⟨E⟩ := nonempty_homology_strictHenselization_iso_of_isIso_higherBaseChangeMapAb B hX
        hS f g x _ q (hbc q)
      let H := DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)
      refine isIso_homology_smallEtaleDerivedGlobalSectionsRestriction_of_iso m
        (pullback.snd π g) A q ?_
      exact H.mapIso ((smallEtaleDerivedGlobalSections Q).mapIso
          (smallEtaleDerivedPullbackAbConstantComplexIso m A ≪≫
            (smallEtaleDerivedPullbackAbConstantComplexIso (pullback.snd (p ≫ f) g) A).symm)) ≪≫
        E ≪≫ H.mapIso ((smallEtaleDerivedGlobalSections P).mapIso
          (smallEtaleDerivedPullbackAbConstantComplexIso (pullback.snd π g) A))
  have := isIso_smallEtaleDerivedGlobalSectionsRestriction (pullback.snd π g)
  have hmsnd : m ≫ pullback.snd π g = pullback.snd (p ≫ f) g :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  exact (isIso_restriction_constantComplex_comp_iff hmsnd A).2 hm'

/-- Restriction of constant coefficients from a geometric point `t` of `Spec 𝒪^{sh}_{S,f(x)}`
to the variety of vanishing cycles is invertible when restriction from `t` to
`Spec 𝒪^{sh}_{X,x} ×_S t` is. -/
private theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_vanishingCyclesFibre_fst
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (x : GeometricPoint X)
    [IsIso (strictHenselizationToBase B S hS (x.map f))]
    (t : GeometricPoint (strictHenselization B S hS (x.map f))) (A : Ab.{u + 1})
    (hQ : IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (pullback.snd (strictHenselizationToBase B X hX x ≫ f)
        (t.hom ≫ strictHenselizationToBase B S hS (x.map f)))).app
      (smallEtaleConstantComplexAb t.source A))) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (pullback.fst t.hom (strictHenselizationSquareMap B hX hS f x))).app
      (smallEtaleConstantComplexAb t.source A)) := by
  let π := strictHenselizationToBase B S hS (x.map f)
  let σ := strictHenselizationSquareMap B hX hS f x
  let p := strictHenselizationToBase B X hX x
  let g : t.source ⟶ S := t.hom ≫ π
  let V := vanishingCyclesFibre B hX hS f x t
  let Q := pullback (p ≫ f) g
  let qV : V ⟶ strictHenselization B X hX x := pullback.snd t.hom σ
  let eV : V ⟶ t.source := pullback.fst t.hom σ
  change IsIso ((smallEtaleDerivedGlobalSectionsRestriction eV).app
    (smallEtaleConstantComplexAb t.source A))
  have : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (pullback.snd (p ≫ f) g)).app
      (smallEtaleConstantComplexAb t.source A)) := hQ
  have hw : qV ≫ p ≫ f = eV ≫ g := by
    refine (congrArg (qV ≫ ·) (strictHenselizationSquareMap_comp B hX hS f x).symm).trans ?_
    change pullback.snd t.hom σ ≫ σ ≫ π = pullback.fst t.hom σ ≫ t.hom ≫ π
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  have hw' : pullback.snd (p ≫ f) g ≫ t.hom = pullback.fst (p ≫ f) g ≫ σ := by
    rw [← cancel_mono π, Category.assoc, Category.assoc, strictHenselizationSquareMap_comp]
    exact pullback.condition.symm
  let φ : V ⟶ Q := pullback.lift qV eV hw
  let ψ : Q ⟶ V := pullback.lift _ _ hw'
  have hψfst : ψ ≫ eV = pullback.snd (p ≫ f) g := pullback.lift_fst _ _ _
  have hψsnd : ψ ≫ qV = pullback.fst (p ≫ f) g := pullback.lift_snd _ _ _
  have hφfst : φ ≫ pullback.fst (p ≫ f) g = qV := pullback.lift_fst _ _ _
  have hφsnd : φ ≫ pullback.snd (p ≫ f) g = eV := pullback.lift_snd _ _ _
  have hφ : IsIso φ := ⟨⟨ψ, by
    apply pullback.hom_ext (f := t.hom) (g := σ)
    · change (φ ≫ ψ) ≫ eV = 𝟙 V ≫ eV
      rw [Category.assoc, hψfst, hφsnd, Category.id_comp]
    · change (φ ≫ ψ) ≫ qV = 𝟙 V ≫ qV
      rw [Category.assoc, hψsnd, hφfst, Category.id_comp], by
    apply pullback.hom_ext
    · rw [Category.assoc, hφfst, hψsnd, Category.id_comp]
    · rw [Category.assoc, hφsnd, hψfst, Category.id_comp]⟩⟩
  have := isIso_smallEtaleDerivedGlobalSectionsRestriction φ
  exact (isIso_restriction_constantComplex_comp_iff hφsnd A).2 inferInstance

/-- Restriction of constant coefficients from `Spec 𝒪^{sh}_{X,x}` to the variety of vanishing
cycles at a geometric point `t` of `Spec 𝒪^{sh}_{S,f(x)}` is invertible when restriction from `t`
to the variety of vanishing cycles is. -/
private theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_vanishingCyclesFibre_snd
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (x : GeometricPoint X)
    (t : GeometricPoint (strictHenselization B S hS (x.map f))) (A : Ab.{u + 1})
    (heV : IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (pullback.fst t.hom (strictHenselizationSquareMap B hX hS f x))).app
      (smallEtaleConstantComplexAb t.source A))) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (pullback.snd t.hom (strictHenselizationSquareMap B hX hS f x))).app
      (smallEtaleConstantComplexAb (strictHenselization B X hX x) A)) := by
  let s := x.map f
  let σ := strictHenselizationSquareMap B hX hS f x
  let qV := pullback.snd t.hom σ
  let eV := pullback.fst t.hom σ
  change IsIso ((smallEtaleDerivedGlobalSectionsRestriction qV).app
    (smallEtaleConstantComplexAb (strictHenselization B X hX x) A))
  have ht : IsIso ((smallEtaleDerivedGlobalSectionsRestriction t.hom).app
      (smallEtaleConstantComplexAb (strictHenselization B S hS s) A)) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction_app_constantComplex_of_strictlyHenselian
      (geometricPointToStrictHenselization B S hS s)
      (geometricPointToStrictHenselization_base_default B S hS s) t.hom A
  have hσA : IsIso ((smallEtaleDerivedGlobalSectionsRestriction σ).app
      (smallEtaleConstantComplexAb (strictHenselization B S hS s) A)) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction_strictHenselizationSquareMap_app hX hS f x _
  have hcond : eV ≫ t.hom = qV ≫ σ := pullback.condition
  rw [← isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_constantComplex_iff qV σ,
    isIso_restriction_constantComplex_comp_iff hcond]
  exact heV

/-- **Local acyclicity of a smooth morphism over its own strict henselization.** Let `f : X ⟶ S`
be a smooth morphism of schemes of a big étale site and `x` a geometric point of `X` such that the
structure morphism of the strict henselization of `S` at `f(x)` is an isomorphism, and let `n` be a
positive integer invertible on `S`. Then `f` is locally acyclic at `x` relative to the constant
sheaf `ℤ/nℤ`. -/
theorem isLocallyAcyclicAt_of_smooth_of_isIso_strictHenselizationToBase
    (h0EYS : FlatReducedFibresBaseChange.{u}) (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) (h0F08 : FirstFailureNormalization.{u})
    (h03SC2 : AffineCurveCohomologyVanishing.{u}) (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) [Smooth f]
    (x : GeometricPoint X) [IsIso (strictHenselizationToBase B S hS (x.map f))]
    (n : ℕ) (hn0 : 0 < n) (hn : IsUnit (((n : ℤ) : Γ(S, ⊤)))) :
    IsLocallyAcyclicAt B hX hS f (smallEtaleConstantZModComplex X n) x := by
  intro t
  let A : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  let s := x.map f
  let π := strictHenselizationToBase B S hS s
  let σ := strictHenselizationSquareMap B hX hS f x
  let p := strictHenselizationToBase B X hX x
  let V := vanishingCyclesFibre B hX hS f x t
  let qV : V ⟶ strictHenselization B X hX x := pullback.snd t.hom σ
  let g : t.source ⟶ S := t.hom ≫ π
  let Fc := (constantSheaf (smallEtaleTopology t.source) Ab.{u + 1}).obj A
  have : IsAffineHom g := inferInstanceAs (IsAffineHom (t.hom ≫ π))
  have : QuasiSeparated g := IsSeparated.instQuasiSeparated g
  have hbc : ∀ q : ℕ, IsIso ((higherBaseChangeMapAb f g (pullback.fst f g) (pullback.snd f g)
      pullback.condition q).app Fc) := fun q =>
    isIso_higherBaseChangeMapAb_of_smooth_of_zsmul_eq_zero h0EYS h0EZR h0EZS h0F08 h03SC2
      h03SC6 h0EYD f (pullback.fst f g) (pullback.snd f g) g
      (IsPullback.of_hasPullback f g) hn Fc (fun U a => zsmul_constantSheaf_zmod_eq_zero _ n U a) q
  have : NeZero n := ⟨hn0.ne'⟩
  have : Finite A := inferInstanceAs (Finite (ULift.{u + 1} (ZMod n)))
  have hQ : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (pullback.snd (p ≫ f) g)).app
      (smallEtaleConstantComplexAb t.source A)) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction_pullback_snd_of_isIso_higherBaseChangeMapAb
      hX hS f x g A hbc
  have hqV : IsIso ((smallEtaleDerivedGlobalSectionsRestriction qV).app
      (smallEtaleConstantComplexAb (strictHenselization B X hX x) A)) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction_vanishingCyclesFibre_snd hX hS f x t A
      (isIso_smallEtaleDerivedGlobalSectionsRestriction_vanishingCyclesFibre_fst hX hS f x t A hQ)
  rw [vanishingCyclesFibreMap_eq]
  exact (isIso_vanishingCyclesMap_app_iff B X hX x qV _).2 ((NatTrans.isIso_app_iff_of_iso _
    (smallEtaleDerivedPullbackAbConstantComplexIso (𝟙 _ ≫ p) A)).2 hqV)

end Stacks.EtaleCohomology.SmoothBaseChange

end
