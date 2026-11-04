module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessFibreSquare

/-!
# The fibre of the openness step of the theorem of the cube

In the notation of `StacksFrontier.AlgebraicGeometry.Cube.OpennessSetup`, let `L` be a
quasi-coherent module on `Q = (X ×_k Y) ×_k Spec R` and let `𝔭` be a prime of `R` over which `L`
is trivial on the fibre. This file proves the degree-zero input of the openness step of the
theorem of the cube ([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)): after base
change to `κ(𝔭)`, a degree-zero cocycle of the Čech complex `C` of `L` whose restriction to the
face `X_R` vanishes is zero.

## Main results

* `Stacks.Cech.cochainBaseChange_square`: the comparison of Čech cochains around a commutative
  square of schemes, read through `pullbackComp` and `pullbackCongr`.
* `Stacks.Cech.exists_global_of_cechD_eq_zero`: a Čech `0`-cocycle is a global section.
* `Stacks.Cech.eq_zero_of_pullbackSections_eq_zero`: a nonzero global section of a trivial
  module on a proper geometrically integral scheme pulls back to a nonzero section along any
  morphism from a nonempty scheme.
* `AlgebraicGeometry.Cube.Openness.h0_fibre`: the degree-zero statement above.

## Implementation notes

The base change of `C` to `κ(𝔭)` is the Čech complex of the fibre `Q_κ`
(`Stacks.Cech.cechBaseChangeData`, which needs `L` quasi-coherent and the opens `W s` affine).
The base change of the face map `ΦX` is compared with the face map of the fibre through
`Stacks.Cech.cochainBaseChange_square`, applied to the square `j_{X,κ} ≫ g_Q = g_X ≫ j_X`; only
a map, not an isomorphism, is needed out of the base change of the face complex, so the face
opens need not be affine. On the fibre a `0`-cocycle is a global section of a trivial module on
a proper geometrically integral scheme over `κ(𝔭)`, hence a constant multiple of the
trivializing section (Stacks Tag 0BUG, part (8)), and a nonzero multiple restricts to a nonzero
section on the nonempty face.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Cube.Openness

open Stacks.Cech

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R]
  {I J : Type u} [Finite I] [Finite J] (UX : I → X.Opens) (UY : J → Y.Opens)
  (hUXa : ∀ a, IsAffineOpen (UX a)) (hUYa : ∀ b, IsAffineOpen (UY b))
  (hUX : (⊤ : X.Opens) = ⨆ a, UX a) (hUY : (⊤ : Y.Opens) = ⨆ b, UY b)
  (L : (Q f g R).Modules) [L.IsQuasicoherent]
  (𝔮 : Ideal R) [𝔮.IsPrime]

include hx hUXa hUYa hUX hUY in
/-- **Degree zero of the fibre.** After base change to the residue field at `𝔭`, a degree-zero
cocycle of the Čech complex `C` of `L` whose restriction to the face `X_R` vanishes is zero,
provided `L` is trivial on the fibre over `𝔭`: on the fibre it is a global section of a trivial
module on a proper geometrically integral scheme, and such a section pulls back to zero on the
nonempty face only if it is zero. -/
theorem h0_fibre (𝔭 : PrimeSpectrum R) (hfib : Nonempty ((Scheme.Modules.pullback (pullback.fst
    (qR f g R)
      (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))).obj L ≅
        SheafOfModules.unit _)) :
    ∀ z : StacksDraft.ConeLift.bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).X 0),
      (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
          ((C f g R UX UY L).d 0 1)).hom z
        = 0 →
      (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
        ((ΦX f g y hy R UX UY L).f 0)).hom z = 0 → z = 0 := by
  intro z hz hΦ
  let ρ := algebraMap R 𝔭.asIdeal.ResidueField
  let D := cechBaseChangeData ρ (qR f g R) (qκ f g R 𝔭.asIdeal) (gQ f g R 𝔭.asIdeal)
    (IsPullback.of_hasPullback _ _) L (W f g R UX UY) (isAffineOpen_W f g R UX UY hUXa hUYa)
    (Wκ f g R UX UY 𝔭.asIdeal) (Equiv.refl _) (fun _ => rfl)
  let zκ := (D.alternatingIso.hom.f 0).hom z
  have hd : ((alternatingCechModuleComplex (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
      ((Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L)).d 0 1).hom zκ = 0 := by
    have := congrArg (fun φ => φ.hom z) (D.alternatingIso.hom.comm 0 1)
    simp only [ModuleCat.hom_comp] at this
    refine this.trans ?_
    show (D.alternatingIso.hom.f 1).hom
      (((ModuleCat.extendScalars ρ).map ((C f g R UX UY L).d 0 1)).hom z) = 0
    rw [show ((ModuleCat.extendScalars ρ).map ((C f g R UX UY L).d 0 1)).hom z = 0 from hz,
      map_zero]
  -- the face map on the fibre
  let M := (Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L
  let Φκ := alternatingCechModuleComplexPullbackMap (qκ f g R 𝔭.asIdeal) (qXκ f R 𝔭.asIdeal)
    (jXκ f g y hy R 𝔭.asIdeal) (jXκ_qκ f g y hy R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
        (Vκ f g y hy R UX UY 𝔭.asIdeal)
    (Vκ_eq f g y hy R UX UY 𝔭.asIdeal) M
  let Tiso : (Scheme.Modules.pullback (jXκ f g y hy R 𝔭.asIdeal)).obj M ≅
      (Scheme.Modules.pullback (gX f R 𝔭.asIdeal)).obj
        ((Scheme.Modules.pullback (jX f g y hy R)).obj L) :=
    (Scheme.Modules.pullbackComp (jXκ f g y hy R 𝔭.asIdeal) (gQ f g R 𝔭.asIdeal)).app L ≪≫
      (Scheme.Modules.pullbackCongr (jXκ_gQ f g y hy R 𝔭.asIdeal)).app L ≪≫
        ((Scheme.Modules.pullbackComp (gX f R 𝔭.asIdeal) (jX f g y hy R)).app L).symm
  let T := (alternatingCechModuleComplexMapIso (qXκ f R 𝔭.asIdeal)
      (Vκ f g y hy R UX UY 𝔭.asIdeal) Tiso).hom.f 0
  let Λ : (ModuleCat.extendScalars ρ).obj ((DX f g y hy R UX UY L).X 0) ⟶
      alternatingCechModuleObj (qXκ f R 𝔭.asIdeal) (Vκ f g y hy R UX UY 𝔭.asIdeal)
        ((Scheme.Modules.pullback (gX f R 𝔭.asIdeal)).obj
          ((Scheme.Modules.pullback (jX f g y hy R)).obj L)) 0 :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ρ
    (Y := alternatingCechModuleObj (qXκ f R 𝔭.asIdeal) (Vκ f g y hy R UX UY 𝔭.asIdeal)
      ((Scheme.Modules.pullback (gX f R 𝔭.asIdeal)).obj
        ((Scheme.Modules.pullback (jX f g y hy R)).obj L)) 0)
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars ρ).obj (alternatingCechModuleObj
      (qXκ f R 𝔭.asIdeal) (Vκ f g y hy R UX UY 𝔭.asIdeal) ((Scheme.Modules.pullback
          (gX f R 𝔭.asIdeal)).obj
        ((Scheme.Modules.pullback (jX f g y hy R)).obj L)) 0))
      (alternatingCochainBaseChangeₗ (gX f R 𝔭.asIdeal)
      (fun s => jX f g y hy R ⁻¹ᵁ W f g R UX UY s) (Vκ f g y hy R UX UY 𝔭.asIdeal) (Equiv.refl _)
      ((Scheme.Modules.pullback (jX f g y hy R)).obj L) (fun _ => rfl) ρ (qX f R)
      (qXκ f R 𝔭.asIdeal) (fun V => baseRingHom_comp_app ρ (qX f R) (qXκ f R 𝔭.asIdeal)
          (gX f R 𝔭.asIdeal)
        (IsPullback.of_hasPullback _ _) V) 0))
  have key : (ModuleCat.extendScalars ρ).map ((ΦX f g y hy R UX UY L).f 0) ≫ Λ =
      D.alternatingIso.hom.f 0 ≫ Φκ.f 0 ≫ T := by
    refine ModuleCat.ExtendScalars.hom_ext fun s => ?_
    have hD := alternatingCechModuleObjBaseChangeIso_hom_one_tmul (gQ f g R 𝔭.asIdeal)
        (W f g R UX UY)
      (Wκ f g R UX UY 𝔭.asIdeal) (Equiv.refl _) L (fun _ => rfl) ρ (qR f g R) (qκ f g R 𝔭.asIdeal)
      (fun V => baseRingHom_comp_app ρ (qR f g R) (qκ f g R 𝔭.asIdeal) (gQ f g R 𝔭.asIdeal)
        (IsPullback.of_hasPullback _ _) V)
      (IsPullback.of_hasPullback _ _) (isAffineOpen_W f g R UX UY hUXa hUYa) 0 s
    have hmap := ModuleCat.ExtendScalars.map_tmul ρ ((ΦX f g y hy R UX UY L).f 0)
      (1 : 𝔭.asIdeal.ResidueField) s
    refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
    refine Eq.trans ?_ (CategoryTheory.comp_apply _ _ _).symm
    refine Eq.trans ?_ (congrArg (Φκ.f 0 ≫ T).hom hD).symm
    refine Eq.trans (congrArg Λ.hom hmap) ?_
    have hΛ : ∀ m, Λ.hom ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[R, ρ] m) =
        alternatingCochainBaseChangeₗ (gX f R 𝔭.asIdeal)
          (fun s => jX f g y hy R ⁻¹ᵁ W f g R UX UY s) (Vκ f g y hy R UX UY 𝔭.asIdeal)
          (Equiv.refl _)
          ((Scheme.Modules.pullback (jX f g y hy R)).obj L) (fun _ => rfl) ρ (qX f R)
          (qXκ f R 𝔭.asIdeal) (fun V => baseRingHom_comp_app ρ (qX f R) (qXκ f R 𝔭.asIdeal)
              (gX f R 𝔭.asIdeal)
            (IsPullback.of_hasPullback _ _) V) 0 m :=
      fun m => one_smul (M := 𝔭.asIdeal.ResidueField) (α := alternatingCechModuleObj
          (qXκ f R 𝔭.asIdeal)
        (Vκ f g y hy R UX UY 𝔭.asIdeal) ((Scheme.Modules.pullback (gX f R 𝔭.asIdeal)).obj
          ((Scheme.Modules.pullback (jX f g y hy R)).obj L)) 0) _
    refine Eq.trans (hΛ _) ?_
    exact Subtype.ext (cochainBaseChange_square (gQ f g R 𝔭.asIdeal) (jX f g y hy R)
      (gX f R 𝔭.asIdeal)
      (jXκ f g y hy R 𝔭.asIdeal) (jXκ_gQ f g y hy R 𝔭.asIdeal) L (W f g R UX UY)
          (Wκ f g R UX UY 𝔭.asIdeal)
      (fun _ => rfl) (fun s => jX f g y hy R ⁻¹ᵁ W f g R UX UY s) (fun _ => rfl)
      (Vκ f g y hy R UX UY 𝔭.asIdeal) (fun _ => rfl) (Vκ_eq f g y hy R UX UY 𝔭.asIdeal) 0
        s.1).symm
  have hT : T.hom ((Φκ.f 0).hom zκ) = 0 := by
    have h := congrArg (fun φ => φ.hom z) key
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans ?_
    show Λ.hom (((ModuleCat.extendScalars ρ).map ((ΦX f g y hy R UX UY L).f 0)).hom z) = 0
    rw [show ((ModuleCat.extendScalars ρ).map ((ΦX f g y hy R UX UY L).f 0)).hom z = 0 from hΦ,
      map_zero]
  have hface0 : (Φκ.f 0).hom zκ = 0 := by
    have h := congrArg ((alternatingCechModuleComplexMapIso (qXκ f R 𝔭.asIdeal)
      (Vκ f g y hy R UX UY 𝔭.asIdeal) Tiso).inv.f 0).hom hT
    rw [map_zero] at h
    refine Eq.trans ?_ h
    show _ = ((T ≫ (alternatingCechModuleComplexMapIso (qXκ f R 𝔭.asIdeal)
      (Vκ f g y hy R UX UY 𝔭.asIdeal) Tiso).inv.f 0).hom ((Φκ.f 0).hom zκ))
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  have hface : cochainBaseChange (jXκ f g y hy R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
      (Vκ f g y hy R UX UY 𝔭.asIdeal)
      (Equiv.refl _) M (Vκ_eq f g y hy R UX UY 𝔭.asIdeal) 0 zκ.1 = 0 :=
    congrArg Subtype.val hface0
  have hU : ⨆ s, Wκ f g R UX UY 𝔭.asIdeal s = ⊤ := by
    refine eq_top_iff.mpr fun p _ => ?_
    have : gQ f g R 𝔭.asIdeal p ∈ ⨆ s, W f g R UX UY s := by
      rw [iSup_W_eq_top f g R UX UY hUX hUY]; trivial
    obtain ⟨s, hs⟩ := Opens.mem_iSup.mp this
    exact Opens.mem_iSup.mpr ⟨s, hs⟩
  have : Surjective f := ⟨fun p => ⟨x p, by
    rw [← Scheme.Hom.comp_apply, hx]; exact Subsingleton.elim _ _⟩⟩
  have : Nonempty (XRκ f R 𝔭.asIdeal) := by
    obtain ⟨p, -⟩ :=
      (qXκ f R 𝔭.asIdeal).surjective (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField)
    exact ⟨p⟩
  let _ := sectionsModule (qκ f g R 𝔭.asIdeal) M ⊤
  let _ := cochainModule (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal) M 0
  let _ := cochainModule (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal) M 1
  obtain ⟨σ, hσ⟩ : zκ ∈ LinearMap.range (sectionsToAlternatingₗ (qκ f g R 𝔭.asIdeal)
      (Wκ f g R UX UY 𝔭.asIdeal) M (fun _ => le_top)) := by
    rw [range_sectionsToAlternatingₗ (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal) M
        (fun _ => le_top)
      hU.ge]
    exact hd
  have hσ0 : σ = 0 := eq_zero_of_cochainBaseChange_restr_eq_zero (qκ f g R 𝔭.asIdeal)
    (jXκ f g y hy R 𝔭.asIdeal) M hfib.some (Wκ f g R UX UY 𝔭.asIdeal) hU
    (Vκ f g y hy R UX UY 𝔭.asIdeal)
    (Vκ_eq f g y hy R UX UY 𝔭.asIdeal) σ (by rw [← hface, ← hσ]; rfl)
  have hzκ : zκ = 0 := by rw [← hσ, hσ0, map_zero]; rfl
  have e : (D.alternatingIso.inv.f 0).hom zκ = z := by
    show ((D.alternatingIso.hom.f 0 ≫ D.alternatingIso.inv.f 0).hom z) = z
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  rw [← e, hzκ, map_zero]
  rfl

include hUXa hUYa hUX hUY in
/-- **Degree one of the fibre.** After base change to the residue field at `𝔭`, a degree-one
cocycle of the Čech complex `C` of `L` whose restrictions to the two faces are coboundaries is a
coboundary, provided `L` is trivial on the fibre over `𝔭`: on the fibre this is the Künneth
lemma `AlgebraicGeometry.Cube.exists_coboundary_of_faces` for `Q_κ = X_{R,κ} ×_κ Y_{R,κ}`, read
through the trivialization of `L`. -/
theorem h1_fibre (𝔭 : PrimeSpectrum R) (hfib : Nonempty ((Scheme.Modules.pullback (pullback.fst
    (qR f g R) (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))).obj L ≅
      SheafOfModules.unit _)) :
    ∀ c : StacksDraft.ConeLift.bcObj (algebraMap R 𝔭.asIdeal.ResidueField)
        ((C f g R UX UY L).X 1),
      (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
        ((C f g R UX UY L).d 1 2)).hom c = 0 →
      ∀ (eX : StacksDraft.ConeLift.bcObj (algebraMap R 𝔭.asIdeal.ResidueField)
          ((DX f g y hy R UX UY L).X 0))
        (eY : StacksDraft.ConeLift.bcObj (algebraMap R 𝔭.asIdeal.ResidueField)
          ((DY f g x hx R UX UY L).X 0)),
      (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
          ((ΦX f g y hy R UX UY L).f 1)).hom c =
        (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
          ((DX f g y hy R UX UY L).d 0 1)).hom eX →
      (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
          ((ΦY f g x hx R UX UY L).f 1)).hom c =
        (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
          ((DY f g x hx R UX UY L).d 0 1)).hom eY →
      ∃ c' : StacksDraft.ConeLift.bcObj (algebraMap R 𝔭.asIdeal.ResidueField)
          ((C f g R UX UY L).X 0),
        (StacksDraft.ConeLift.bcMap (algebraMap R 𝔭.asIdeal.ResidueField)
          ((C f g R UX UY L).d 0 1)).hom c' = c := by
  intro c hc eX eY hX hY
  let ρ := algebraMap R 𝔭.asIdeal.ResidueField
  let D := cechBaseChangeData ρ (qR f g R) (qκ f g R 𝔭.asIdeal) (gQ f g R 𝔭.asIdeal)
    (IsPullback.of_hasPullback _ _) L (W f g R UX UY) (isAffineOpen_W f g R UX UY hUXa hUYa)
    (Wκ f g R UX UY 𝔭.asIdeal) (Equiv.refl _) (fun _ => rfl)
  let cκ := (D.alternatingIso.hom.f 1).hom c
  have hd : ((alternatingCechModuleComplex (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
      ((Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L)).d 1 2).hom cκ = 0 := by
    have := congrArg (fun φ => φ.hom c) (D.alternatingIso.hom.comm 1 2)
    simp only [ModuleCat.hom_comp] at this
    refine this.trans ?_
    show (D.alternatingIso.hom.f 2).hom
      (((ModuleCat.extendScalars ρ).map ((C f g R UX UY L).d 1 2)).hom c) = 0
    rw [show ((ModuleCat.extendScalars ρ).map ((C f g R UX UY L).d 1 2)).hom c = 0 from hc,
      map_zero]
  obtain ⟨eXκ, heXκ⟩ := exists_face_coboundary ρ (qR f g R) (qκ f g R 𝔭.asIdeal)
    (gQ f g R 𝔭.asIdeal) (IsPullback.of_hasPullback _ _) (qX f R) (qXκ f R 𝔭.asIdeal)
    (gX f R 𝔭.asIdeal) (IsPullback.of_hasPullback _ _) (jX f g y hy R) (jX_qR f g y hy R)
    (jXκ f g y hy R 𝔭.asIdeal) (jXκ_qκ f g y hy R 𝔭.asIdeal) (jXκ_gQ f g y hy R 𝔭.asIdeal) L
    (W f g R UX UY) (isAffineOpen_W f g R UX UY hUXa hUYa) c eX hX
  obtain ⟨eYκ, heYκ⟩ := exists_face_coboundary ρ (qR f g R) (qκ f g R 𝔭.asIdeal)
    (gQ f g R 𝔭.asIdeal) (IsPullback.of_hasPullback _ _) (qY g R) (qYκ g R 𝔭.asIdeal)
    (gY g R 𝔭.asIdeal) (IsPullback.of_hasPullback _ _) (jY f g x hx R) (jY_qR f g x hx R)
    (jYκ f g x hx R 𝔭.asIdeal) (jYκ_qκ f g x hx R 𝔭.asIdeal) (jYκ_gQ f g x hx R 𝔭.asIdeal) L
    (W f g R UX UY) (isAffineOpen_W f g R UX UY hUXa hUYa) c eY hY
  obtain ⟨c'κ, hc'κ⟩ := exists_cechD_eq_of_faces (isPullback_Qκ f g R 𝔭.asIdeal)
    (xκ f x hx R 𝔭.asIdeal) (xκ_qXκ f x hx R 𝔭.asIdeal)
    (yκ g y hy R 𝔭.asIdeal) (yκ_qYκ g y hy R 𝔭.asIdeal)
    (UXκ f R 𝔭.asIdeal UX) (UYκ g R 𝔭.asIdeal UY)
    (isAffineOpen_UXκ f R 𝔭.asIdeal UX hUXa) (isAffineOpen_UYκ g R 𝔭.asIdeal UY hUYa)
    (iSup_UXκ f R 𝔭.asIdeal UX hUX) (iSup_UYκ g R 𝔭.asIdeal UY hUY)
    (Wκ f g R UX UY 𝔭.asIdeal) (Wκ_eq_W f g R 𝔭.asIdeal UX UY)
    ((Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L) hfib.some
    (jXκ f g y hy R 𝔭.asIdeal) (jXκ_eq_faceX f g y hy R 𝔭.asIdeal) _
    (preimage_face_eq (gQ f g R 𝔭.asIdeal) (gX f R 𝔭.asIdeal) (jX f g y hy R)
      (jXκ f g y hy R 𝔭.asIdeal) (jXκ_gQ f g y hy R 𝔭.asIdeal) (W f g R UX UY))
    (jYκ f g x hx R 𝔭.asIdeal) (jYκ_eq_faceY f g x hx R 𝔭.asIdeal) _
    (preimage_face_eq (gQ f g R 𝔭.asIdeal) (gY g R 𝔭.asIdeal) (jY f g x hx R)
      (jYκ f g x hx R 𝔭.asIdeal) (jYκ_gQ f g x hx R 𝔭.asIdeal) (W f g R UX UY))
    cκ.1 (congrArg Subtype.val hd) eXκ.1 (congrArg Subtype.val heXκ) eYκ.1
    (congrArg Subtype.val heYκ)
  let c'' : (alternatingCechModuleComplex (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
      ((Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L)).X 0 :=
    ⟨c'κ, ⟨fun i hi => absurd (fun a b _ => Fin.ext (by have := a.2; have := b.2; omega)) hi,
      fun _ a b hab => absurd (Fin.ext (by have := a.2; have := b.2; omega)) hab⟩⟩
  refine ⟨(D.alternatingIso.inv.f 0).hom c'', ?_⟩
  have hcomm := congrArg (fun φ => φ.hom c'') (D.alternatingIso.inv.comm 0 1)
  simp only [ModuleCat.hom_comp] at hcomm
  show ((ModuleCat.extendScalars ρ).map ((C f g R UX UY L).d 0 1)).hom
    ((D.alternatingIso.inv.f 0).hom c'') = c
  refine hcomm.trans ?_
  have hd' : ((alternatingCechModuleComplex (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
      ((Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L)).d 0 1).hom c'' = cκ :=
    Subtype.ext hc'κ
  show (D.alternatingIso.inv.f 1).hom
    (((alternatingCechModuleComplex (qκ f g R 𝔭.asIdeal) (Wκ f g R UX UY 𝔭.asIdeal)
      ((Scheme.Modules.pullback (gQ f g R 𝔭.asIdeal)).obj L)).d 0 1).hom c'') = c
  rw [hd']
  show ((D.alternatingIso.hom.f 1 ≫ D.alternatingIso.inv.f 1).hom c) = c
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rfl

end AlgebraicGeometry.Cube.Openness

end

end
