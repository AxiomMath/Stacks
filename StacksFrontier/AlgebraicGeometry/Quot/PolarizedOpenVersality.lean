module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFormalEffective
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.Deformation.Artin.Versality.DiagonalFibreEffective
public import StacksFrontier.Deformation.Artin.Versality.OpennessEffectiveTowers

/-!
# Openness of versality for `𝒫olarized`

The stack `𝒫olarized` of polarized proper flat families of finite presentation (Stacks 0D1M),
over the big fppf site of a locally Noetherian terminal base scheme such as `Spec ℤ`, satisfies
openness of versality (Stacks 07XQ): if an object over a scheme `U` locally of finite type is
versal at a finite type point `u₀`, it is versal at every finite type point of an open
neighbourhood of `u₀`.

The proof is the source's. Artin's criterion for openness of versality, Stacks 0CXU, applies:
the diagonal of `𝒫olarized` is representable by algebraic spaces (Stacks 0D42), `𝒫olarized`
satisfies (RS*) (Stacks 0D44) and is limit preserving (Stacks 0D43), and condition (4) of 0CXU,
the effectivity of systems over inverse systems of rings with square-zero transition kernels,
is a special case of Grothendieck's existence theorem in the form of strong formal effectiveness
for polarized schemes (Stacks 0D4T).

## Main results

* `AlgebraicGeometry.hasEffectiveThickeningTowers_polarizedSliceProjection`: towers of
  first-order thickenings in `𝒫olarized` are effective, by Stacks 0D4T.
* `AlgebraicGeometry.isOpenVersality_polarizedStackUnconditional`: openness of versality for
  `𝒫olarized` over a locally Noetherian terminal base scheme.
* `AlgebraicGeometry.isOpenVersality_polarizedStack_specULiftZ`: openness of versality for
  `𝒫olarized` over `Spec ℤ`, the first assertion of Stacks 0D4V.

## Implementation notes

Condition (4) of Stacks 0CXU is used in the form in which its proof uses it
(`Deformation.Artin.HasEffectiveThickeningTowers`): a tower `x ⟶ x₁ ⟶ x₂ ⟶ ⋯` over first-order
thickenings `U ⟶ Uₙ` of an affine scheme, with closed immersions as steps, maps compatibly to one
object over a first-order thickening of `U`. The rings `Rₙ = Γ(Uₙ)` then form an inverse system
with surjective transition maps whose kernels square to zero, the levels of the tower are the
data of Stacks 0D4T over it, and the algebraization Stacks 0D4T produces over `Spec (lim Rₙ)` is
the required object.

## References

* [Stacks Project, Tag 0D4V](https://stacks.math.columbia.edu/tag/0D4V)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Ample

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (hT : IsTerminal (B.obj hS))

/-- **Towers of first-order thickenings in `𝒫olarized` are effective.** Let
`x ⟶ x₁ ⟶ x₂ ⟶ ⋯` be a tower of polarized families over first-order thickenings `U ⟶ Uₙ` of an
affine scheme `U`, whose steps lie over closed immersions. Then there are a polarized family `ξ`
and morphisms `xₙ ⟶ ξ` compatible with the steps of the tower, such that `U ⟶ T` is a first-order
thickening, `T` being the base of `ξ`.

The rings `Rₙ = Γ(Uₙ)` form an inverse system with surjective transition maps whose kernels
square to zero, and `ξ` is the algebraization over `T = Spec (lim Rₙ)` of the levels of the tower
given by Stacks 0D4T. -/
theorem hasEffectiveThickeningTowers_polarizedSliceProjection (good : S.Opens → Prop) :
    Deformation.Artin.HasEffectiveThickeningTowers B S hS (polarizedSliceProjection B hS hT)
      good := by
  classical
  intro x xs step fromX hfromS hxaff _ _ hthick hstep
  let q := polarizedSliceProjection B hS hT
  let VS := BigFppfOver.toScheme B S hS
  have : IsAffine (VS.obj (q.obj x)) := hxaff
  -- the tower as a functor out of `ℕ`
  let Xs : ℕ ⥤ PolarizedFamily B := Functor.ofSequence (fun n => step (n + 1))
  let Tn := Xs ⋙ q
  have hTaff : ∀ n, IsAffine (B.inclusion.obj (xs (n + 1)).base) := fun n =>
    Stacks.Thickenings.isAffine_of_isThickening (hthick n).isThickening
  have := hTaff
  have hTaffT : ∀ n, IsAffine (VS.obj (Tn.obj n)) := hTaff
  have hTaffQ : ∀ n, IsAffine (VS.obj (q.obj (xs (n + 1)))) := hTaff
  have hTaffX : ∀ n, IsAffine (VS.obj (q.obj (Xs.obj n))) := hTaff
  have hXs : ∀ n, Xs.map (homOfLE (Nat.le_succ n)) = step (n + 1) := fun n =>
    Functor.ofSequence_map_homOfLE_succ _ n
  let g : ∀ n, x ⟶ Xs.obj n := fun n => fromX (n + 1)
  have hfromX : ∀ {i j : ℕ} (f : i ⟶ j), g i ≫ Xs.map f = g j := fun f =>
    Deformation.Artin.comp_map_of_succ Xs g (fun n => by
      show fromX (n + 1 + 1) = fromX (n + 1) ≫ Xs.map (homOfLE (Nat.le_succ n))
      rw [hXs]
      exact hfromS (n + 1)) f
  have hclosed : ∀ {i j : ℕ} (f : i ⟶ j), IsClosedImmersion (VS.map (Tn.map f)) := fun f =>
    Deformation.Artin.isClosedImmersion_map_of_succ (q ⋙ VS) Xs (fun n => by
      rw [Functor.comp_map, hXs]
      exact hstep n) f
  -- the inverse system of rings and its limit
  let F : ℕᵒᵖ ⥤ CommRingCat.{u} := Tn.op ⋙ VS.op ⋙ Scheme.Γ
  have hFmap : ∀ n, F.map (homOfLE (Nat.le_succ n)).op =
      (B.inclusion.map (step (n + 1)).baseMap).appTop := by
    intro n
    show (VS.map (q.map (Xs.map (homOfLE (Nat.le_succ n))))).appTop = _
    rw [hXs]
    rfl
  have hFc : ∀ n : ℕᵒᵖ, B.Contains (Spec (F.obj n)) := by
    intro n
    have h : Scheme.size (B.inclusion.obj (xs (n.unop + 1)).base) < B.cutoff :=
      (xs (n.unop + 1)).base.2
    rw [Scheme.size_of_isAffine] at h
    show Scheme.size (Spec (F.obj n)) < B.cutoff
    rwa [Scheme.size_Spec]
  have hRc : B.Contains (Spec (limit F)) := Deformation.Artin.contains_spec_limit B F hFc
  have hsurjΓ : ∀ {i j : ℕ} (f : i ⟶ j), Function.Surjective (VS.map (Tn.map f)).appTop := by
    intro i j f
    have := hclosed f
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (VS.map (Tn.map f))).2
  have hqfac : ∀ {i j : ℕ} (f : i ⟶ j), (VS.map (q.map (g j))).appTop =
      (VS.map (Tn.map f)).appTop ≫ (VS.map (q.map (g i))).appTop := by
    intro i j f
    have e : q.map (g i) ≫ Tn.map f = q.map (g j) :=
      (q.map_comp _ _).symm.trans (congrArg q.map (hfromX f))
    rw [← Scheme.Hom.comp_appTop, ← VS.map_comp, e]
  have hkerΓ : ∀ {i j : ℕ} (f : i ⟶ j),
      RingHom.ker (VS.map (Tn.map f)).appTop.hom ^ 2 = ⊥ := by
    intro i j f
    have hk := Deformation.Artin.ker_appTop_sq_of_isFirstOrderThickening _ (hthick j)
    refine le_bot_iff.mp ((Ideal.pow_right_mono ?_ 2).trans hk.le)
    intro z hz
    have hz' : (VS.map (Tn.map f)).appTop.hom z = 0 := hz
    show (VS.map (q.map (g j))).appTop.hom z = 0
    rw [hqfac f, CommRingCat.comp_apply, hz', map_zero]
  have hsurj : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom :=
    fun n => hsurjΓ (homOfLE (Nat.le_succ n))
  have hnil : ∀ n : ℕ, RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤
      nilradical (F.obj (op (n + 1))) := by
    intro n z hz
    refine mem_nilradical.mpr ⟨2, ?_⟩
    have h2 : z ^ 2 ∈ RingHom.ker (VS.map (Tn.map (homOfLE (Nat.le_succ n)))).appTop.hom ^ 2 :=
      Ideal.pow_mem_pow hz 2
    rw [hkerΓ] at h2
    exact Ideal.mem_bot.mp h2
  -- the levels of the tower as data of Stacks 0D4T
  let isoS : ∀ n, B.inclusion.obj (xs (n + 1)).base ≅ Spec (F.obj (op n)) := fun n =>
    (B.inclusion.obj (xs (n + 1)).base).isoSpec
  have hnat : ∀ n : ℕ, B.inclusion.map (step (n + 1)).baseMap ≫ (isoS (n + 1)).hom =
      (isoS n).hom ≫ Spec.map (F.map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    rw [hFmap n]
    exact (Scheme.isoSpec_hom_naturality _).symm
  have hpb : ∀ n : ℕ, IsPullback (step (n + 1)).totalMap
      ((xs (n + 1)).toBase ≫ (isoS n).hom) ((xs (n + 1 + 1)).toBase ≫ (isoS (n + 1)).hom)
      (Spec.map (F.map (homOfLE (Nat.le_succ n)).op)) := by
    intro n
    refine (step (n + 1)).cartesian.of_iso (Iso.refl _) (Iso.refl _) (isoS n) (isoS (n + 1))
      ?_ ?_ ?_ (hnat n) <;> simp
  have hproper : ∀ n, IsProper (xs n).toBase := fun n => (xs n).proper
  have hflat : ∀ n, Flat (xs n).toBase := fun n => (xs n).flat
  have hfp : ∀ n : ℕ, FinitePresentation ((xs (n + 1)).toBase ≫ (isoS n).hom) := by
    intro n
    obtain ⟨_, _, _⟩ := (xs (n + 1)).finitePresentation
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hinv : ∀ n, IsInvertibleModule (xs n).total (xs n).lineBundle := fun n =>
    (xs n).invertible
  have hample : IsAmple (xs (0 + 1)).total (xs (0 + 1)).lineBundle :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mp
      (xs (0 + 1)).relativelyAmple
  obtain ⟨Y, gY, ℒ, hℒ, j, hj, e, hproperY, hflatY, hfpY, hampleY, hpbY, hiso, hcompat⟩ :=
    Stacks.PolarizedAlgebraization.exists_algebraization F hsurj hnil
      (fun n => (xs (n + 1)).total)
      (fun n => (xs (n + 1)).toBase ≫ (isoS n).hom)
      (fun n => (step (n + 1)).totalMap) hpb (fun n => (xs (n + 1)).lineBundle)
      (fun n => (step (n + 1)).lineBundleIso) (hproper := fun _ => inferInstance)
      (hflat := fun _ => inferInstance) hfp hample
  have := hproperY
  have := hflatY
  have := hℒ
  have : IsAffine (B.inclusion.obj (B.obj hRc)) := inferInstanceAs (IsAffine (Spec (limit F)))
  -- the algebraization as a polarized family over `Spec (lim Rₙ)`
  let ξ : PolarizedFamily B :=
    { base := B.obj hRc
      total := Y
      toBase := gY
      proper := hproperY
      flat := hflatY
      finitePresentation := hfpY
      lineBundle := ℒ
      invertible := hℒ
      relativelyAmple :=
        (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mpr hampleY }
  let legS : ∀ n, B.inclusion.obj (xs (n + 1)).base ⟶ Spec (limit F) := fun n =>
    (isoS n).hom ≫ Spec.map (limit.π F (op n))
  let ι : ∀ n, xs (n + 1) ⟶ ξ := fun n =>
    ({ baseMap := ObjectProperty.homMk (X := (xs (n + 1)).base) (Y := B.obj hRc) (legS n)
       totalMap := j n
       cartesian := by
         show IsPullback (j n) (xs (n + 1)).toBase gY (legS n)
         refine (hpbY n).of_iso (Iso.refl _) (Iso.refl _)
           (isoS n).symm (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [legS]
       lineBundleIso := @asIso _ _ _ _ (e n) (hiso n) } : PolarizedFamily.Hom (xs (n + 1)) ξ)
  refine ⟨ξ, ι, fun n => ?_, ?_⟩
  · refine PolarizedFamily.Hom.ext ?_ (hj n) ?_
    · apply B.inclusion.map_injective
      show B.inclusion.map (step (n + 1)).baseMap ≫ (isoS (n + 1)).hom ≫
          Spec.map (limit.π F (op (n + 1))) = (isoS n).hom ≫ Spec.map (limit.π F (op n))
      rw [← Category.assoc, hnat n, Category.assoc, ← Spec.map_comp, limit.w]
    · refine PolarizedFormal.heq_of_pullbackCongr_hom_app_comp (hj n) _ _ ?_
      show (Scheme.Modules.pullbackCongr (hj n)).hom.app ℒ ≫ e n =
        (Scheme.Modules.pullbackComp _ _).inv.app ℒ ≫
          (Scheme.Modules.pullback (step (n + 1)).totalMap).map (e (n + 1)) ≫
            (step (n + 1)).lineBundleIso.hom
      rw [← hcompat n, ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
        Category.id_comp]
  · -- `U ⟶ Spec (lim Rₙ)` is a first-order thickening
    let a : B.inclusion.obj x.base ⟶ B.inclusion.obj (xs (0 + 1)).base :=
      B.inclusion.map (fromX (0 + 1)).baseMap
    show Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map ((fromX (0 + 1)).baseMap ≫ (ι 0).baseMap))
    rw [Functor.map_comp]
    show Stacks.Thickenings.IsFirstOrderThickening (a ≫ legS 0)
    have : IsAffine (B.inclusion.obj x.base) := hxaff
    have ha : Stacks.Thickenings.IsFirstOrderThickening a := hthick 0
    have : IsClosedImmersion a := ha.1
    let πn : ∀ n, limit F ⟶ Γ(B.inclusion.obj (xs (n + 1)).base, ⊤) := fun n =>
      limit.π F (op n)
    have hlegS0 : (legS 0).appTop = (Scheme.ΓSpecIso (limit F)).hom ≫ πn 0 :=
      Deformation.Artin.appTop_isoSpec_hom_comp_specMap (πn 0)
    have happ : (a ≫ legS 0).appTop = (Scheme.ΓSpecIso (limit F)).hom ≫ πn 0 ≫ a.appTop := by
      rw [Scheme.Hom.comp_appTop, hlegS0, Category.assoc]
    have hq₀ : Function.Surjective a.appTop :=
      (IsClosedImmersion.isAffine_surjective_of_isAffine _).2
    have hπ₀ : Function.Surjective (πn 0) := by
      have hl := isLimitOfPreserves (forget CommRingCat) (limit.isLimit F)
      refine Types.surjective_π_app_zero_of_surjective_map hl (fun n => ?_)
      exact hsurjΓ (homOfLE (Nat.le_succ n))
    have hker : RingHom.ker (πn 0 ≫ a.appTop).hom ^ 2 = ⊥ :=
      Deformation.Artin.ker_limit_π_comp_sq_eq_bot F
        (fun n => (VS.map (q.map (g n))).appTop) (fun f => hqfac f)
        (fun n => Deformation.Artin.ker_appTop_sq_of_isFirstOrderThickening _ (hthick n))
    refine Deformation.Artin.isFirstOrderThickening_of_appTop _ ?_ ?_
    · rw [happ]
      exact (hq₀.comp hπ₀).comp (ConcreteCategory.bijective_of_isIso _).2
    · rw [happ]
      exact Deformation.Artin.ker_comp_sq_eq_bot _ (ConcreteCategory.bijective_of_isIso _).1 _ hker

variable (B hS) in
/-- **Openness of versality for `𝒫olarized`.** Over the big fppf site of a locally Noetherian
terminal base scheme `S`, the stack `𝒫olarized` satisfies openness of versality: if an object
over a scheme `U` locally of finite type over `S` is versal at a finite type point `u₀`, it is
versal at every finite type point of an open neighbourhood of `u₀`.

This is Stacks 0CXU applied with Stacks 0D42 (the diagonal), 0D44 (condition (RS*)), 0D43 (limit
preservation) and 0D4T (effectivity of towers,
`AlgebraicGeometry.hasEffectiveThickeningTowers_polarizedSliceProjection`). -/
theorem isOpenVersality_polarizedStackUnconditional [IsLocallyNoetherian S] :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : (polarizedStackUnconditional B hS hT).val.obj)
        (hx : ((polarizedStackUnconditional B hS hT).val.p ⋙ Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        Deformation.Artin.IsVersalAt U
          ((polarizedStackUnconditional B hS hT).val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            Deformation.Artin.IsVersalAt U
              ((polarizedStackUnconditional B hS hT).val.p ⋙ Over.post B.inclusion) u x hx :=
  Deformation.Artin.isOpenVersality_of_hasEffectiveThickeningTowers B S hS
    (polarizedStackUnconditional B hS hT)
    (hasRepresentableDiagonal_polarizedStackUnconditional B hS hT)
    (satisfiesRSStar_polarizedSliceProjection B hS hT)
    (isLimitPreservingPolarizedUnconditional B hS hT)
    (hasEffectiveThickeningTowers_polarizedSliceProjection hT IsAffineOpen)

variable (B) in
/-- **Openness of versality for `𝒫olarized` over `Spec ℤ`.** The stack `𝒫olarized` over the big
fppf site of `Spec ℤ` satisfies openness of versality: if an object over a scheme `U` locally of
finite type is versal at a finite type point `u₀`, it is versal at every finite type point of an
open neighbourhood of `u₀`. This is the first assertion of Stacks 0D4V. -/
theorem isOpenVersality_polarizedStack_specULiftZ
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    ∀ (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))), LocallyOfFiniteType U.hom →
      ∀ (x : (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.obj)
        (hx : ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
          Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        Deformation.Artin.IsVersalAt U
          ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
            Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            Deformation.Artin.IsVersalAt U
              ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
                Over.post B.inclusion) u x hx := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact isOpenVersality_polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)

end AlgebraicGeometry

end
