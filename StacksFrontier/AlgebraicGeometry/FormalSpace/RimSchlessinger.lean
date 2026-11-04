module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FunctorForm
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCovering
import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
import StacksFrontier.AlgebraicGeometry.FormalSpace.PushoutSections
import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFormallyEtale
import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.NilpotentLift
import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective
import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas
import StacksFrontier.Deformation.Artin.RimSchlessinger.CoconeUniqueFlat

/-!
# Condition (RS) for a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space over
`S`. This file proves that `X` satisfies the Rim–Schlessinger condition (RS) of Stacks 07WP in
the functor form `Deformation.Artin.SatisfiesRSFunctor`: for a pushout `Y' = Y ⨿_{X₀} X₀'` of
spectra of Artinian local rings of finite type over `S` along a closed immersion `X₀ ⟶ X₀'`,
every pair of sections of `X` over `Y` and `X₀'` agreeing over `X₀` comes from exactly one
section over `Y'`.

This is the input from the formal algebraic space `W` in the proof of Stacks 0GI6.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesRSFunctor_of_isFormalAlgebraicSpace`: a formal
  algebraic space satisfies condition (RS).

## Implementation notes

The source deduces the statement for `W` from Stacks 07WQ, applied to the algebraic spaces
`W_n` of a presentation `W = colim W_n` (Stacks 0GHM): a point of `W` over the spectrum of an
Artinian local ring with `𝔪ⁿ = 0` is a point of `W_n`. The library proves Stacks 0GHM only for
a Noetherian affine formal algebraic space, so the argument here avoids the `W_n` and instead
follows the proof of Stacks 07WQ directly on an affine formal étale atlas `Xᵢ ⟶ X`, in the form
of `Deformation.Artin.nonempty_cocone_of_atlas_of_hasLiftsAlong`:

1. *Uniqueness* holds for any sheaf whose morphisms from represented sheaves are relatively
   representable (`AlgebraicGeometry.FormalSpace.eq_of_isPushout`), which is Stacks 0AIP for a
   formal algebraic space.
2. The section over `Y` lifts to a member `Xᵢ` of the atlas over an affine étale `A ⟶ Y`
   (`AlgebraicGeometry.FormalSpace.exists_etale_affine_chart`); since `Y` has a single point, this
   one chart covers `Y`. By the topological invariance of the étale site
   (`AlgebraicGeometry.BigFppfOver.exists_etale_covering_lift_of_isThickening`) it extends to an
   affine étale covering `V ⟶ Y'`.
3. Over the base change of the square along `V ⟶ Y'`, which is again a pushout
   (`Deformation.Artin.isPushout_toScheme_baseChange_of_flat`), the lift over the first middle
   corner extends across the thickening into the second one because `Xᵢ ⟶ X` is formally étale
   (`AlgebraicGeometry.FormalSpace.formallyEtale_hom_of_isRepresentableEtale` and
   `AlgebraicGeometry.Space.FormallySmooth.exists_isLift_of_isNilpotent`), and the two lifts glue
   in the affine formal algebraic space `Xᵢ`
   (`AlgebraicGeometry.FormalSpace.exists_eq_of_isPushout_of_isAffineFormalAlgebraicSpace`).
4. The resulting section over `V` descends to `Y'` by the sheaf property, its two restrictions to
   `V ×_{Y'} V` agreeing by uniqueness at the base-changed square.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0GI6](https://stacks.math.columbia.edu/tag/0GI6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- The underlying scheme of an affine scheme whose ring of global sections is Artinian and
local has a single point. -/
theorem subsingleton_of_isArtinianRing_of_isLocalRing (Y : Scheme.{u}) [IsAffine Y]
    [IsLocalRing Γ(Y, ⊤)] [IsArtinianRing Γ(Y, ⊤)] : Subsingleton Y := by
  have : Subsingleton (Spec Γ(Y, ⊤)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Γ(Y, ⊤)))
  exact (Scheme.homeoOfIso Y.isoSpec).injective.subsingleton

/-- **Equality of sections after the base change of a single covering morphism.** Let `τ : V ⟶ Y'`
generate a covering sieve of the big fppf site of `S` and let `j : Y ⟶ Y'`. Two sections of an
fppf sheaf over `Y` whose restrictions to `Y ×_{Y'} V` agree are equal. -/
theorem eq_of_map_pullback_fst_eq (X : FppfSheaf B S hS) {Y Y' V : BigFppfOver B S hS}
    (j : Y ⟶ Y') (τ : V ⟶ Y')
    (hτ : Sieve.generate (Presieve.singleton τ) ∈ BigFppfOver.topology B S hS Y')
    {s t : X.obj.obj (op Y)}
    (h : X.obj.map (pullback.fst j τ).op s = X.obj.map (pullback.fst j τ).op t) : s = t := by
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ X.obj).1 X.property
  refine (hsheaf _ ((BigFppfOver.topology B S hS).pullback_stable j hτ)).isSeparatedFor.ext ?_
  rintro T f ⟨Z, l, g', ⟨⟩, hfac⟩
  let p : T ⟶ pullback j τ := pullback.lift f l hfac.symm
  have hp : p ≫ pullback.fst j τ = f := pullback.lift_fst _ _ _
  rw [← hp, op_comp, Functor.map_comp, types_comp_apply, types_comp_apply, h]

/-- **A formal algebraic space satisfies condition (RS).** Let `X` be a formal algebraic space
over `S`. For every pushout `Y' = Y ⨿_{X₀} X₀'` of spectra of Artinian local rings of finite type
over `S` along a closed immersion `X₀ ⟶ X₀'`, every pair of sections of `X` over `Y` and `X₀'`
agreeing over `X₀` is the pair of restrictions of exactly one section over `Y'`. -/
theorem satisfiesRSFunctor_of_isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) : Deformation.Artin.SatisfiesRSFunctor B S hS X.obj := by
  classical
  intro X₀ X₀' Y Y' i j i' j' w hX₀ hX₀' hY hY' _ _ _ _ hci hpo a b hab
  let T := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  have hrel := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX
  have hpoB : IsPushout i j i' j' := IsPushout.of_map T w hpo
  refine existsUnique_of_exists_of_unique ?_
    (fun t t' ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ => eq_of_isPushout hrel hpoB (h₂.trans h₂'.symm)
      (h₁.trans h₁'.symm))
  have : IsAffine (T.obj X₀) := hX₀.1
  have : IsAffine (T.obj X₀') := hX₀'.1
  have : IsAffine (T.obj Y) := hY.1
  have : IsAffine (T.obj Y') := hY'.1
  have : IsLocalRing Γ(T.obj X₀, ⊤) := hX₀.2.1
  have : IsLocalRing Γ(T.obj Y, ⊤) := hY.2.1
  have : IsLocalRing Γ(T.obj X₀', ⊤) := hX₀'.2.1
  have : IsLocalRing Γ(T.obj Y', ⊤) := hY'.2.1
  have : IsArtinianRing Γ(T.obj X₀', ⊤) := hX₀'.2.2
  have : IsArtinianRing Γ(T.obj Y, ⊤) := hY.2.2
  have : IsArtinianRing Γ(T.obj Y', ⊤) := hY'.2.2
  -- the square of global sections is cartesian, and both legs are thickenings
  have hΓ : IsPullback (T.map j').appTop (T.map i').appTop (T.map j).appTop (T.map i).appTop := by
    have := (hpo.map Scheme.Γ.rightOp).unop.flip
    simpa [T] using this.flip
  have hisurj : Function.Surjective (T.map i).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (T.map i)).2
  have hgt := Deformation.Artin.isThickening_of_surjective_appTop_of_isArtinianRing (T.map i)
    hisurj
  have hit := Deformation.Artin.isThickening_of_surjective_appTop_of_isArtinianRing (T.map j')
    (Deformation.Artin.surjective_of_isPullback hΓ hisurj)
  let Q : BaseSquare (BigFppfOver B S hS) := ⟨X₀, Y, X₀', Y', j, i, j', i', w.symm⟩
  -- an affine étale chart of `Y` through which `a` lifts to a member of the atlas
  obtain ⟨-, I, Xi, fi, hXi, hfi, hsurj⟩ := hX
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : Subsingleton (T.obj Y) := subsingleton_of_isArtinianRing_of_isLocalRing (T.obj Y)
  let y₀ : T.obj Y := (Scheme.homeoOfIso (T.obj Y).isoSpec).symm (IsLocalRing.closedPoint _)
  obtain ⟨R, hR, hRmem⟩ := Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc fi hsurj a
  obtain ⟨V, g, hg, z₀, hz₀⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hR y₀
  obtain ⟨k, t, ht⟩ := hRmem g hg
  obtain ⟨hrep, het⟩ := hfi k
  obtain ⟨A, c, φ, hA, hc, hcy, hφ⟩ := exists_etale_affine_chart B S hS (fi k) hrep het Y
    (uliftYonedaEquiv.symm a) V g (uliftYonedaEquiv.symm t) (by
      rw [uliftYonedaEquiv_symm_comp, ht, uliftYonedaEquiv_symm_map]; rfl) z₀
  have : IsAffine (T.obj A) := hA
  have : Etale (T.map c) := hc
  -- it extends to an affine étale covering of `Y'`
  obtain ⟨Vc, τc, ιc, hτe, hVa, hιc, hcov⟩ :=
    BigFppfOver.exists_etale_covering_lift_of_isThickening B S hS j' hit (I := PUnit.{u + 2})
      (fun _ => A) (fun _ => c) (fun _ => hc) (fun _ => hA) (fun y => ⟨PUnit.unit, by
        rw [Subsingleton.elim y (g.left.hom z₀)]; exact hcy⟩)
  let V₁ := Vc PUnit.unit
  let τ : V₁ ⟶ Y' := τc PUnit.unit
  let ι : pullback j' τ ⟶ A := ιc PUnit.unit
  have hι : ι ≫ c = pullback.fst j' τ := hιc PUnit.unit
  have : Etale (T.map τ) := hτe PUnit.unit
  have : IsAffine (T.obj V₁) := hVa PUnit.unit
  have hsingle : Sieve.generate (Presieve.singleton τ) ∈ J Y' := by
    refine J.superset_covering ?_ hcov
    rintro Z f ⟨W', l, g', ⟨⟨⟩⟩, hfac⟩
    exact ⟨_, l, τ, Presieve.singleton.mk, hfac⟩
  -- the base change of the square along `τ`
  let Qk := Q.baseChange τ
  let aQ := Q.baseChangeHom τ
  have sY : IsPullback (T.map Qk.i) (T.map aQ.aV) (T.map τ) (T.map Q.i) :=
    (Q.isPullback_baseChange_i τ).map T
  have sX' : IsPullback (T.map Qk.j) (T.map aQ.aW) (T.map τ) (T.map Q.j) :=
    (Q.isPullback_baseChange_j τ).map T
  have sX'' : IsPullback (T.map Qk.g) (T.map aQ.aU) (T.map aQ.aW) (T.map Q.g) :=
    (Q.isPullback_baseChange_g τ).map T
  have : IsAffine (T.obj Qk.V) := IsAffine.of_isPullback sY
  have : IsAffine (T.obj Qk.W) := IsAffine.of_isPullback sX'
  have : _root_.AlgebraicGeometry.IsClosedImmersion (T.map i) := hci
  have hci' : _root_.AlgebraicGeometry.IsClosedImmersion (T.map Qk.g) :=
    MorphismProperty.of_isPullback sX''.flip hci
  have hthk : Stacks.Thickenings.IsThickening (T.map Qk.g) :=
    Stacks.Thickenings.isThickening_of_isPullback sX'' hgt
  have : Etale (T.map aQ.aW) := MorphismProperty.of_isPullback sX' inferInstance
  let : Algebra Γ(T.obj X₀', ⊤) Γ(T.obj Qk.W, ⊤) := (T.map aQ.aW).appTop.hom.toAlgebra
  have : Algebra.Etale Γ(T.obj X₀', ⊤) Γ(T.obj Qk.W, ⊤) :=
    HasRingHomProperty.appTop @Etale _ inferInstance
  have : Module.Finite Γ(T.obj X₀', ⊤) Γ(T.obj Qk.W, ⊤) := Module.Finite.of_quasiFinite
  have : IsArtinianRing Γ(T.obj Qk.W, ⊤) := IsArtinianRing.of_finite Γ(T.obj X₀', ⊤) _
  have hnil : IsNilpotent (RingHom.ker (T.map Qk.g).appTop.hom) := by
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(T.obj Qk.W, ⊤)
    refine ⟨n, le_bot_iff.1 ?_⟩
    calc RingHom.ker (T.map Qk.g).appTop.hom ^ n ≤ nilradical Γ(T.obj Qk.W, ⊤) ^ n :=
          Ideal.pow_right_mono (fun _ ha => mem_nilradical.2
            (hthk.isNilpotent_of_mem_ker_appTop ha)) n
      _ = ⊥ := by rw [hn, Ideal.zero_eq_bot]
  -- the lift over the first middle corner, and its extension to the second
  let ℓV : (Xi k).obj.obj (op Qk.V) := (Xi k).obj.map ι.op (uliftYonedaEquiv φ)
  have hℓV : (fi k).hom.app _ ℓV = X.obj.map aQ.aV.op a := by
    have h := congrArg uliftYonedaEquiv hφ
    rw [uliftYonedaEquiv_comp, show uliftYoneda.map c ≫ uliftYonedaEquiv.symm a =
      uliftYonedaEquiv.symm (X.obj.map c.op a) from (uliftYonedaEquiv_symm_map c.op a).symm,
      Equiv.apply_symm_apply] at h
    rw [(fi k).hom.naturality_apply, h, ← X.obj.map_comp_apply, ← op_comp, hι]
  have hFS : Space.FormallySmooth (fi k).hom := fun T₁ T₂ h₁ h₂ m hm x y hxy =>
    (formallyEtale_hom_of_isRepresentableEtale (fi k) ⟨hrep, het⟩ T₁ T₂ h₁ h₂ m hm x y hxy).exists
  have hcompU : (fi k).hom.app _ ((Xi k).obj.map Qk.f.op ℓV) =
      X.obj.map Qk.g.op (X.obj.map aQ.aW.op b) := by
    rw [(fi k).hom.naturality_apply, hℓV, ← X.obj.map_comp_apply, ← X.obj.map_comp_apply,
      ← op_comp, ← op_comp, aQ.wf, aQ.wg, op_comp, op_comp, X.obj.map_comp_apply,
      X.obj.map_comp_apply]
    exact congrArg _ hab
  obtain ⟨ℓW, hℓW₁, hℓW₂⟩ := hFS.exists_isLift_of_isNilpotent Qk.g hci' hnil _ _ hcompU
  -- the two lifts glue in the affine formal chart
  have hpoQk : IsPushout Qk.f Qk.g Qk.i Qk.j :=
    IsPushout.of_map T Qk.w (Deformation.Artin.isPushout_toScheme_baseChange_of_flat B S hS Q
      hΓ hgt τ)
  obtain ⟨ζ, hζV, hζW⟩ := exists_eq_of_isPushout_of_isAffineFormalAlgebraicSpace (hXi k) hpoQk
    ℓV ℓW hℓW₁.symm
  let z₁ : X.obj.obj (op V₁) := (fi k).hom.app _ ζ
  have hz₁V : X.obj.map Qk.i.op z₁ = X.obj.map aQ.aV.op a := by
    rw [← hℓV, ← hζV, (fi k).hom.naturality_apply]
  have hz₁W : X.obj.map Qk.j.op z₁ = X.obj.map aQ.aW.op b := by
    rw [← hℓW₂, ← hζW, (fi k).hom.naturality_apply]
  -- the two restrictions of `z₁` to `V₁ ×_{Y'} V₁` agree
  let π₁ := pullback.fst τ τ
  let π₂ := pullback.snd τ τ
  have sq₁ := (IsPullback.of_hasPullback τ τ).map T
  have : IsAffine (T.obj (pullback τ τ)) := IsAffine.of_isPullback sq₁
  have : Flat (T.map π₁) :=
    MorphismProperty.of_isPullback sq₁.flip (inferInstanceAs (Flat (T.map τ)))
  have : Flat (T.map (π₁ ≫ τ)) := by rw [T.map_comp]; infer_instance
  let Q₂ := Q.baseChange (π₁ ≫ τ)
  have hpoQ₂ : IsPushout Q₂.f Q₂.g Q₂.i Q₂.j :=
    IsPushout.of_map T Q₂.w (Deformation.Artin.isPushout_toScheme_baseChange_of_flat B S hS Q
      hΓ hgt (π₁ ≫ τ))
  have hres : ∀ (t : pullback τ τ ⟶ V₁) (ht : t ≫ τ = π₁ ≫ τ),
      X.obj.map Q₂.i.op (X.obj.map t.op z₁) = X.obj.map (Q.baseChangeHom (π₁ ≫ τ)).aV.op a ∧
        X.obj.map Q₂.j.op (X.obj.map t.op z₁) =
          X.obj.map (Q.baseChangeHom (π₁ ≫ τ)).aW.op b := by
    intro t ht
    let m := Q.baseChangeMap t ht
    have hmV : m.aV ≫ aQ.aV = (Q.baseChangeHom (π₁ ≫ τ)).aV :=
      congrArg BaseSquare.Hom.aV (Q.baseChangeMap_comp_baseChangeHom t ht)
    have hmW : m.aW ≫ aQ.aW = (Q.baseChangeHom (π₁ ≫ τ)).aW :=
      congrArg BaseSquare.Hom.aW (Q.baseChangeMap_comp_baseChangeHom t ht)
    have hwi : Q₂.i ≫ t = m.aV ≫ Qk.i := m.wi
    have hwj : Q₂.j ≫ t = m.aW ≫ Qk.j := m.wj
    constructor
    · rw [← X.obj.map_comp_apply, ← op_comp, hwi, op_comp,
        X.obj.map_comp_apply, hz₁V, ← X.obj.map_comp_apply, ← op_comp, hmV]
    · rw [← X.obj.map_comp_apply, ← op_comp, hwj, op_comp,
        X.obj.map_comp_apply, hz₁W, ← X.obj.map_comp_apply, ← op_comp, hmW]
  have hover : X.obj.map π₁.op z₁ = X.obj.map π₂.op z₁ := by
    obtain ⟨h₁V, h₁W⟩ := hres π₁ rfl
    obtain ⟨h₂V, h₂W⟩ := hres π₂ pullback.condition.symm
    exact eq_of_isPushout hrel hpoQ₂ (h₁V.trans h₂V.symm) (h₁W.trans h₂W.symm)
  -- descent of `z₁` along `τ`
  have hsheaf : Presieve.IsSheafFor X.obj (Presieve.singleton τ) :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type J X.obj).1 X.property _ hsingle)
  obtain ⟨z, hz, -⟩ := Presieve.isSheafFor_singleton.1 hsheaf z₁ (fun p₁ p₂ hp => by
    calc X.obj.map p₁.op z₁ = X.obj.map (pullback.lift p₁ p₂ hp).op (X.obj.map π₁.op z₁) := by
          rw [← X.obj.map_comp_apply, ← op_comp, pullback.lift_fst]
      _ = X.obj.map (pullback.lift p₁ p₂ hp).op (X.obj.map π₂.op z₁) := by rw [hover]
      _ = X.obj.map p₂.op z₁ := by
          rw [← X.obj.map_comp_apply, ← op_comp, pullback.lift_snd])
  have hfin : ∀ {U : BigFppfOver B S hS} (m : U ⟶ Y') (s : X.obj.obj (op U)),
      X.obj.map (pullback.fst m τ).op s = X.obj.map (pullback.snd m τ).op z₁ →
        X.obj.map m.op z = s := fun m s h => by
    refine eq_of_map_pullback_fst_eq X m τ hsingle ?_
    rw [← X.obj.map_comp_apply, ← op_comp, pullback.condition, op_comp, X.obj.map_comp_apply, hz]
    exact h.symm
  exact ⟨z, hfin j' _ hz₁V.symm, hfin i' _ hz₁W.symm⟩

end AlgebraicGeometry.FormalSpace
