module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsKernelEtaleLocal
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeExceptional
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsDerivedHomology
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDegreeBound
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HigherDirectImageModels

/-!
# The kernel of the restriction of forms to the zero section of the coordinate cone

In the standard situation of Section 50.16 of the source — `A = R[x₁, …, x_m, y₁, …, y_n]`,
`X = Spec A`, the cone `b : L = Proj(⨁_d A_{≥ d}) ⟶ X`, which is the blowup of `X` along
`Z = Spec(A₀)`, its zero section `0 : P = Proj(A) ⟶ L` and the cone projection `π : L ⟶ P` —
write `𝒦^a_L` for the kernel of the restriction of forms `ρ : Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}`.

Clause (3) of [Stacks, Tag 0FUR] says that the comparison `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` is
an isomorphism on cohomology sheaves in positive degrees. This file shows that this is
equivalent to the vanishing of `R^q b_*𝒦^a_L` for `q ≥ 1`, the form in which clause (3) is
transported to the coordinate situation of an arbitrary base for [Stacks, Tag 0FUU]. The only
input beyond the long exact cohomology sequence of `0 ⟶ 𝒦^a_L ⟶ Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S} ⟶ 0`
is that `b_*ρ` is an epimorphism, which holds because the zero section is a section of the cone
projection: `0^*π^*ω = ω` for every form `ω` on `P`.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.epi_homology_zero_derivedPushforward_map`:
  `H⁰(Rf_*(-[0]))` is `f_*`, so it carries a map `g` with `f_*g` an epimorphism to an
  epimorphism.
* `Stacks.DeRham.CoordinateCone.epi_pushforward_coneFormsRestriction`: `b_*ρ` is an
  epimorphism.
* `Stacks.DeRham.isZero_homology_derivedPushforward_kernel_of_isIso_formsDerivedComparisonOf`:
  a comparison `Rb_*F ⟶ i_*Rp_*G` invertible on `H^q` for `q ≥ 1`, attached to an epimorphism
  `r : F ⟶ j_*G` with `b_*r` an epimorphism, gives `H^q(Rb_*(ker r)) = 0` for `q ≥ 1`; for the
  cone this turns clause (3) of [Stacks, Tag 0FUR] into the vanishing of `R^q b_*𝒦^a_L`.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle (unit compIso)

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### `H⁰` of a derived direct image -/

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y))]
  [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))]

/-- **`H⁰(Rf_*(ℱ[0])) ≅ f_*ℱ`, naturally in `ℱ`**: the cohomology in degree `0` of the derived
direct image of a sheaf placed in degree `0` is `R⁰f_*ℱ`, which is `f_*ℱ` because `f_*` is left
exact. -/
def homologyZeroDerivedPushforwardSingleIso :
    DerivedCategory.singleFunctor _ 0 ⋙ derivedPushforward f ⋙
        DerivedCategory.homologyFunctor _ 0 ≅ modulePushforward f :=
  haveI : PreservesLimitsOfSize.{0, 0} (modulePushforward f) :=
    (modulePullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  haveI : PreservesFiniteLimits (modulePushforward f) := inferInstance
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight (boundedDerivedPushforwardIso f).symm
        (DerivedCategory.homologyFunctor _ 0)) ≪≫
    ((modulePushforward f).isoRightDerivedPlusSingle 0).symm

/-- **`H⁰(Rf_*(-[0]))` carries a map whose direct image is an epimorphism to an epimorphism.** -/
theorem epi_homology_zero_derivedPushforward_map
    {M N : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (g : M ⟶ N) [Epi ((modulePushforward f).map g)] :
    Epi ((DerivedCategory.homologyFunctor _ 0).map
      ((derivedPushforward f).map
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).map
          g))) := by
  have heq : (DerivedCategory.homologyFunctor _ 0).map
      ((derivedPushforward f).map
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).map
          g)) =
        (homologyZeroDerivedPushforwardSingleIso f).hom.app M ≫ (modulePushforward f).map g ≫
          (homologyZeroDerivedPushforwardSingleIso f).inv.app N :=
    (NatIso.naturality_2 (homologyZeroDerivedPushforwardSingleIso f) g).symm
  rw [heq]
  exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _
    (@epi_comp _ _ _ _ _ _ ‹_› _ (IsIso.epi_of_iso _))

/-- `epi_homology_zero_derivedPushforward_map` for a morphism of schemes, with the hypothesis on
the direct image of sheaves of modules on schemes. -/
theorem epi_homology_zero_derivedPushforward_map_of_epi_pushforward {X' Y' : Scheme.{u}}
    (f' : X' ⟶ Y') [HasDerivedCategory (ModuleSheaves X'.toRingedSpace)]
    [HasDerivedCategory (ModuleSheaves Y'.toRingedSpace)]
    [EnoughInjectives (ModuleSheaves X'.toRingedSpace)] {M N : X'.Modules} (g : M ⟶ N)
    (hg : Epi ((Scheme.Modules.pushforward f').map g)) :
    Epi ((DerivedCategory.homologyFunctor _ 0).map
      ((derivedPushforward f'.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor (ModuleSheaves X'.toRingedSpace) 0).map g))) :=
  have : Epi ((modulePushforward f'.toLRSHom.toShHom).map g) := hg
  epi_homology_zero_derivedPushforward_map _ g

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-! ### Restricting forms along a section -/

namespace AlgebraicGeometry.Scheme.Hom

/-- **Restricting forms along a section is onto global sections.** If `g : W ⟶ X` is a section
of `p : X ⟶ W`, then every global form `ω` on `W` is the restriction along `g` of the global
form `p^*ω` on `X`. -/
theorem surjective_formsDirectImageComparison_app_top {X W S : Scheme.{u}} (g : W ⟶ X)
    (p : X ⟶ W) (hgp : g ≫ p = 𝟙 W) (π : X ⟶ S) (hp : p ≫ (g ≫ π) = π ≫ 𝟙 S) (d : ℤ) :
    Function.Surjective (Scheme.Modules.Hom.app (formsDirectImageComparison g π d) ⊤) :=
  fun t => ⟨relativeDifferentialFormsPullback p (g ≫ π) π (𝟙 S) hp d ⊤ t,
    (formsDirectImageComparison_app_apply g π d ⊤ _).trans
      (relativeDifferentialFormsPullback_comp_eq_id_top p g (g ≫ π) π hp (by simp) hgp d t)⟩

/-- **Over an affine base, a direct image of a map onto global sections is an epimorphism**, when
the direct image of its target is quasi-coherent. -/
theorem epi_pushforward_map_of_surjective_app_top {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X)
    {M N : Y.Modules} (φ : M ⟶ N) [((Scheme.Modules.pushforward f).obj N).IsQuasicoherent]
    (h : Function.Surjective (Scheme.Modules.Hom.app φ ⊤)) :
    Epi ((Scheme.Modules.pushforward f).map φ) :=
  AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen _
    fun _ => ⟨⊤, isAffineOpen_top _, trivial, fun t => h t⟩

end AlgebraicGeometry.Scheme.Hom

/-! ### The converse of `isIso_homology_formsDerivedComparisonOf_of_isIso` -/

namespace Stacks.DeRham

section Converse

variable {L X P Z : Scheme.{u}}
  [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves L.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves P.toRingedSpace)]
  (b : L ⟶ X) (j : P ⟶ L) (p : P ⟶ Z) (i : Z ⟶ X)
  (w : j.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = p.toLRSHom.toShHom ≫ i.toLRSHom.toShHom)
  {F : L.Modules} (G : P.Modules) (r : F ⟶ (Scheme.Modules.pushforward j).obj G)

/-- **`Rb_*r` is invertible on `H^q` as soon as the comparison `Rb_*F ⟶ i_*Rp_*G` is**, for `j`
a closed immersion: every factor of the comparison after `Rb_*r` is an isomorphism. -/
theorem isIso_homology_derivedPushforward_map_single_of_isIso_formsDerivedComparisonOf
    [IsClosedImmersion j] (q : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ q).map
      (formsDerivedComparisonOf b j p i w G r))) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward b.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor (ModuleSheaves L.toRingedSpace) 0).map r))) := by
  have hu := BlowupTriangle.isIso_unit_of_isClosedEmbedding j.toLRSHom.toShHom j.isClosedEmbedding
    (singleComplex G)
  let H := DerivedCategory.homologyFunctor (ModuleSheaves X.toRingedSpace) q
  let Rb := derivedPushforward b.toLRSHom.toShHom
  let Φ := DerivedCategory.Q ⋙ Rb ⋙ H
  let A := (HomologicalComplex.single (ModuleSheaves L.toRingedSpace) (ComplexShape.up ℤ) 0).map r
  let B := (HomologicalComplex.singleMapHomologicalComplex (modulePushforward j.toLRSHom.toShHom)
    (ComplexShape.up ℤ) 0).inv.app G
  have hB : IsIso (Φ.map B) := (Φ.mapIso ((HomologicalComplex.singleMapHomologicalComplex
    (modulePushforward j.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app G).symm).isIso_hom
  let T := (compIso j.toLRSHom.toShHom b.toLRSHom.toShHom).inv.app _ ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj
      (DerivedCategory.Q.obj (singleComplex G))) w) ≫
    (compIso p.toLRSHom.toShHom i.toLRSHom.toShHom).hom.app _
  have h₁ : IsIso (H.map (Rb.map (DerivedCategory.Q.map (formsRestrictionComplexMap j G r) ≫
      unit j.toLRSHom.toShHom (singleComplex G)))) := by
    have e : H.map (formsDerivedComparisonOf b j p i w G r) =
        H.map (Rb.map (DerivedCategory.Q.map (formsRestrictionComplexMap j G r) ≫
          unit j.toLRSHom.toShHom (singleComplex G))) ≫ H.map T := by
      rw [← H.map_comp]
      rfl
    rw [e] at h
    exact IsIso.of_isIso_comp_right _ (H.map T)
  have h₂ : IsIso (Φ.map (A ≫ B)) := by
    rw [Rb.map_comp, H.map_comp] at h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (Φ.map (A ≫ B)) _ inferInstance h₁
  have hAB : IsIso (Φ.map A ≫ Φ.map B) := (congrArg (fun f => IsIso f) (Φ.map_comp A B)).mp h₂
  have hA : IsIso (Φ.map A) := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hB hAB
  let e := (Rb ⋙ H).mapArrow.mapIso (Arrow.isoOfNatIso (DerivedCategory.singleFunctorIsoCompQ
    (ModuleSheaves L.toRingedSpace) 0) (Arrow.mk r))
  exact (Arrow.isIso_hom_iff_isIso_hom_of_isIso e.hom).2 hA

omit [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves P.toRingedSpace)] in
/-- **Isomorphisms on `H^q(Rb_*-)` in positive degrees and an epimorphism on `H⁰` kill the higher
direct images of the kernel**: for an epimorphism `r : F ⟶ N` of `𝒪_L`-modules, if
`H^q(Rb_*r)` is invertible for `q ≥ 1` and onto for `q = 0`, then `H^q(Rb_*(ker r)) = 0` for
`q ≥ 1`, by the long exact sequence of `0 ⟶ ker r ⟶ F ⟶ N ⟶ 0`. -/
theorem isZero_homology_derivedPushforward_kernel_of_isIso {N : L.Modules} (r : F ⟶ N) [Epi r]
    (h : ∀ q : ℤ, 1 ≤ q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward b.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor (ModuleSheaves L.toRingedSpace) 0).map r))))
    (h₀ : Epi ((DerivedCategory.homologyFunctor _ 0).map
      ((derivedPushforward b.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor (ModuleSheaves L.toRingedSpace) 0).map r))))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedPushforward b.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (ModuleSheaves L.toRingedSpace) 0).obj (kernel r)))) := by
  let b' := b.toLRSHom.toShHom
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing L.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward b')
    (derivedPushforwardUnit b')
    (HomotopyCategory.quasiIso (ModuleSheaves L.toRingedSpace) (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward b').IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward b') _
      (derivedPushforwardUnit b')
  have hS : (ShortComplex.mk (kernel.ι r) r (kernel.condition r)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact r)
      (inferInstanceAs (Mono (kernel.ι _))) inferInstance
  exact hS.isZero_homologyFunctor_obj_X₁_of_isIso (derivedPushforward b') h h₀ q hq

/-- **The comparison invertible on `H^q` in positive degrees kills the higher direct images of
the kernel**: for `j` a closed immersion and `r : F ⟶ j_*G` an epimorphism with `b_*r` an
epimorphism, if the comparison `Rb_*F ⟶ i_*Rp_*G` attached to `r` is invertible on `H^q` for every
`q ≥ 1`, then `H^q(Rb_*(ker r)) = 0` for every `q ≥ 1`. -/
theorem isZero_homology_derivedPushforward_kernel_of_isIso_formsDerivedComparisonOf
    [IsClosedImmersion j] [Epi r] (hb : Epi ((Scheme.Modules.pushforward b).map r))
    (h : ∀ q : ℤ, 1 ≤ q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      (formsDerivedComparisonOf b j p i w G r)))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedPushforward b.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (ModuleSheaves L.toRingedSpace) 0).obj (kernel r)))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing L.toRingedSpace)
  exact isZero_homology_derivedPushforward_kernel_of_isIso b r
    (fun k hk => isIso_homology_derivedPushforward_map_single_of_isIso_formsDerivedComparisonOf
      b j p i w G r k (h k hk))
    (epi_homology_zero_derivedPushforward_map_of_epi_pushforward b r hb) q hq

end Converse

end Stacks.DeRham

namespace Stacks.DeRham.CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

open Stacks.AlgebraicGeometry.ProjAndSpec Scheme.Hom
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation (truncationConeData)

/-! ### The restriction of forms to the zero section is onto -/

/-- **The restriction of forms to the zero section is an epimorphism**: it is the unit of
`0^* ⊣ 0_*`, surjective for the closed immersion `0`, followed by `0_*` of the surjection
`0^*Ω^a_{L/S} ⟶ Ω^a_{P/S}`, and `0_*` is exact. -/
theorem epi_coneFormsRestriction (a : ℕ) : Epi (coneFormsRestriction R m n (a : ℤ)) := by
  have := isClosedImmersion_zeroSection (truncationConeData (yGrading R m n))
  have h₁ := Stacks.ClosedImmersion.epi_unit_app (zeroSection (truncationConeData (yGrading R m n)))
    (Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ))
  have : PreservesFiniteColimits
      (Scheme.Modules.pushforward (zeroSection (truncationConeData (yGrading R m n)))) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward
      (zeroSection (truncationConeData (yGrading R m n))).toLRSHom.toShHom
      (zeroSection (truncationConeData (yGrading R m n))).isClosedEmbedding
  have h₂ := Scheme.Hom.epi_relativeDifferentialFormsMap
    (zeroSection (truncationConeData (yGrading R m n))) (coneToBase R m n) (by simp) a
  rw [coneFormsRestriction, Scheme.Hom.formsDirectImageComparison]
  infer_instance

/-- **`𝒦^a_L`**, the kernel of the restriction of forms `Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}`: the sheaf of
`a`-forms on the cone which vanish on the zero section. -/
abbrev coneFormsKernel (a : ℤ) :=
  kernel (coneFormsRestriction R m n a)

/-- **The sequence `0 ⟶ 𝒦^a_L ⟶ Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S} ⟶ 0` is exact.** -/
theorem shortExact_coneFormsKernel (a : ℕ) :
    (ShortComplex.mk (kernel.ι (coneFormsRestriction R m n (a : ℤ)))
      (coneFormsRestriction R m n (a : ℤ)) (kernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.kernelSequence_exact (coneFormsRestriction R m n (a : ℤ)))
    (inferInstanceAs (Mono (kernel.ι _))) (epi_coneFormsRestriction R m n a)

/-- The cone projection lies over the base: `π ≫ 0 ≫ (L ⟶ S) = (L ⟶ S)`. -/
theorem coneProjection_comp_coneZeroSection_comp_coneToBase :
    pi (truncationConeData (yGrading R m n)) ≫
        (zeroSection (truncationConeData (yGrading R m n)) ≫ coneToBase R m n) =
      coneToBase R m n ≫ 𝟙 _ := by
  have h0 : zeroSection (truncationConeData (yGrading R m n)) ≫ coneToBase R m n =
      coneBundleToBase R m n := by
    simp only [coneBundleToBase, coneCentreToBase, coneToBase, coneToAmbient]
    rw [← Category.assoc, zeroSection_comp_toSpecA]
    simp
  rw [h0]
  simp only [coneBundleToBase, coneCentreToBase, coneToBase, coneToAmbient]
  rw [← Category.assoc, pi_comp_toSpecZero, Category.assoc]
  have := xToZ_comp_zToX_comp_toBase R m n
  simp only [Category.comp_id] at this ⊢
  rw [this]

/-- **`b_*ρ` is an epimorphism.** The restriction of forms is the comparison map on direct
images of forms along `0` followed by an isomorphism. Both sides of the comparison map have
quasi-coherent direct images on the affine `X`, so it is enough that it is onto global sections;
and a global form `ω` on `P` is the restriction of the global form `π^*ω` on `L`, because the zero
section is a section of the cone projection. -/
theorem epi_pushforward_coneFormsRestriction (a : ℕ) :
    Epi ((Scheme.Modules.pushforward (coneToAmbient R m n)).map
      (coneFormsRestriction R m n (a : ℤ))) := by
  have := isClosedImmersion_zeroSection (truncationConeData (yGrading R m n))
  have hN := AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward
    (coneToAmbient R m n) _
    (AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward
      (zeroSection (truncationConeData (yGrading R m n))) _
      (Scheme.Hom.isQuasicoherent_relativeDifferentialForms
        (zeroSection (truncationConeData (yGrading R m n)) ≫ coneToBase R m n) a))
  have h₁ := epi_pushforward_map_of_surjective_app_top (coneToAmbient R m n) _
    (surjective_formsDirectImageComparison_app_top _ _ (zeroSection_comp_pi _) _
      (coneProjection_comp_coneZeroSection_comp_coneToBase R m n) (a : ℤ))
  rw [coneFormsRestriction, Functor.map_comp]
  infer_instance

end Stacks.DeRham.CoordinateCone

end
