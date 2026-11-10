module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening

/-!
# A thickening of a Noetherian algebraic space has finite order

Let `X` be an algebraic space over a scheme `S` which has a surjective étale chart `V ⟶ X` by a
Noetherian scheme. Then every thickening `Z ⊂ X` is a finite order thickening: the defining ideal
of `Z` consists of nilpotent functions on each affine étale chart, the nilradical of the
Noetherian scheme `V` is nilpotent with one exponent
(`Stacks.Divisors.exists_nilradical_pow_eq_bot`), and every étale chart of `X` is covered by
affine étale charts which map to affine opens of `V`, on which the defining ideal of `Z` is
extended from that of the affine open of `V`.

This is the step of the proof that a thickening of an affine algebraic space is affine which
passes from the reductions of the stages of a Noetherian approximation to finite order
thickenings, where `AlgebraicGeometry.Space.isAffineSpace_of_isNthOrderThickening` applies.

## Main results

* `AlgebraicGeometry.Space.isNthOrderThickening_of_atlas`: a thickening of an algebraic space with
  a surjective étale chart whose nilradical has vanishing `(n+1)`st power is an `n`th order
  thickening.
* `AlgebraicGeometry.Space.isFiniteOrderThickening_of_atlas`: a thickening of an algebraic space
  with a surjective étale chart by a Noetherian scheme is a finite order thickening.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- In a ring whose nilradical has vanishing `(n+1)`st power, an ideal of nilpotent elements has
vanishing `(n+1)`st power. -/
theorem _root_.Ideal.pow_eq_bot_of_forall_isNilpotent {A : Type*} [CommRing A] {I : Ideal A}
    (hI : ∀ a ∈ I, IsNilpotent a) {n : ℕ} (hn : _root_.nilradical A ^ (n + 1) = ⊥) :
    I ^ (n + 1) = ⊥ :=
  le_bot_iff.1 ((Ideal.pow_right_mono (fun a ha => hI a ha) (n + 1)).trans (le_of_eq hn))

/-- The image of an ideal with vanishing `m`th power under a ring map has vanishing `m`th power. -/
private theorem map_pow_eq_bot {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {I : Ideal A}
    {m : ℕ} (h : I ^ m = ⊥) : Ideal.map φ I ^ m = ⊥ := by
  rw [← Ideal.map_pow, h, Ideal.map_bot]

/-- The nilradical of a ring isomorphic to a ring whose nilradical has vanishing `(n+1)`st
power has vanishing `(n+1)`st power. -/
theorem _root_.nilradical_pow_eq_bot_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) {n : ℕ} (hn : _root_.nilradical A ^ (n + 1) = ⊥) :
    _root_.nilradical B ^ (n + 1) = ⊥ := by
  have hmap : (_root_.nilradical A).map (e : A →+* B) = _root_.nilradical B := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) fun b hb => ?_
    · exact mem_nilradical.2 ((mem_nilradical.1 ha).map (e : A →+* B))
    have hb : e.symm b ∈ _root_.nilradical A := mem_nilradical.2 ((mem_nilradical.1 hb).map
      (e.symm : B →+* A))
    have := Ideal.mem_map_of_mem (e : A →+* B) hb
    simpa using this
  rw [← hmap]
  exact map_pow_eq_bot _ hn

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The defining ideal of a thickening at an affine étale chart consists of nilpotent
functions. -/
theorem isNilpotent_of_mem_definingIdealAt_of_isThickening {X : AlgebraicSpaces B S hS}
    {R : Subfunctor X.1} (hR : IsThickening B S hS X R) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left))
    (a : ToType ((structureRingSheaf B S hS X).obj.obj (op U)))
    (ha : a ∈ definingIdealAt B S hS X ⟨R, hR.1⟩ (op U)) : IsNilpotent a := by
  have : Mono (IsThickening.inclusion B S hS hR).hom := inferInstanceAs (Mono R.ι)
  have hth : IsThickeningHom B S hS (IsThickening.inclusion B S hS hR) := by
    refine (isThickeningHom_iff_of_mono _).2 ?_
    rw [show Subfunctor.range (IsThickening.inclusion B S hS hR).hom = R from
      Subfunctor.range_ι R]
    exact hR
  rw [definingIdealAt_eq_ker_fSharp] at ha
  exact isNilpotent_of_fSharp_app_eq_zero_of_isAffine B S hS
    (IsThickening.inclusion B S hS hR) hR.1.2 hth.surjective U hU a ha

/-- **A thickening of an algebraic space with a surjective étale chart whose nilradical has
vanishing `(n+1)`st power is an `n`th order thickening.** Every étale chart of `X` is covered by
affine étale charts mapping to affine opens of the chart `V`; on such a chart the defining ideal
is extended from the defining ideal on the affine open of `V`, which consists of nilpotent
functions, whose `(n+1)`st power vanishes. -/
theorem isNthOrderThickening_of_atlas {X : AlgebraicSpaces B S hS} {R : Subfunctor X.1}
    (hR : IsThickening B S hS X R) (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ X.1)
    (hbS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b)
    (hbE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b)
    {n : ℕ} (hn : ((BigFppfOver.toScheme B S hS).obj V).nilradical ^ (n + 1) = ⊥) :
    IsNthOrderThickening B S hS n X R := by
  classical
  refine ⟨hR, fun U => ?_⟩
  obtain ⟨W₀, p, α, hcomm, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj U)) X.2
      (U.1.hom ≫ (𝟙 X : X ⟶ X).hom) V b hbS hbE
  have hp₀ : yoneda.map (Yoneda.fullyFaithful.preimage p) = p :=
    Yoneda.fullyFaithful.map_preimage p
  have hpP : ∀ P : MorphismProperty Scheme.{u},
      MorphismProperty.presheaf (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
        p → P ((BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimage p)) :=
    fun P h => MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) (F := yoneda)
      (by rw [hp₀]; exact h)
  have hpEt : Etale ((BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimage p)) :=
    hpP _ hpE
  have hpSu : Surjective ((BigFppfOver.toScheme B S hS).map
      (Yoneda.fullyFaithful.preimage p)) := hpP _ hpS
  set dglob : ChartDiagram B S hS X.1 X.1 (𝟙 X : X ⟶ X).hom :=
    { U := ⟨CostructuredArrow.mk
          (yoneda.map (Yoneda.fullyFaithful.preimage p) ≫ U.1.hom),
        etale_comp_of_scheme B S hS _ U.1.hom hpEt U.property⟩
      V := ⟨CostructuredArrow.mk b, hbE⟩
      g := α
      comm := by
        have hsq : (yoneda.map (Yoneda.fullyFaithful.preimage p) ≫ U.1.hom) ≫
            (𝟙 X : X ⟶ X).hom = yoneda.map α ≫ b := by
          rw [Category.assoc, hp₀]; exact hcomm
        exact hsq }
  set WtoU : dglob.U ⟶ U :=
    ObjectProperty.homMk
      (CostructuredArrow.homMk (Yoneda.fullyFaithful.preimage p) rfl)
  let J := Σ P : ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj dglob.V)).affineOpens,
      { O : ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj dglob.U)).affineOpens //
        (O : _) ≤ (BigFppfOver.toScheme B S hS).map dglob.g ⁻¹ᵁ (P : _) }
  let W : J → SmallEtale B S hS X.1 := fun i => openChart B S hS X.1 dglob.U (i.2.1 : _)
  let a : ∀ i, W i ⟶ U := fun i => openChartInclusion B S hS X.1 dglob.U (i.2.1 : _) ≫ WtoU
  have hcov : Sieve.ofArrows W a ∈ SmallEtale.topology B S hS X.1 U := by
    refine SmallEtale.ofArrows_mem_topology B S hS X.1 _ _ ?_
    rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
    refine ⟨fun x => ?_, fun i => etale_toScheme_toOver_map B S hS X.1 _⟩
    obtain ⟨w, hw⟩ := hpSu.surj x
    obtain ⟨P, hP, hvP, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj dglob.V)))
        (show (BigFppfOver.toScheme B S hS).map dglob.g w ∈ (⊤ : _) from trivial)
    obtain ⟨O, hO, hwO, hsub⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj dglob.U)))
        (show w ∈ (BigFppfOver.toScheme B S hS).map dglob.g ⁻¹ᵁ P from hvP)
    refine ⟨⟨⟨P, hP⟩, ⟨⟨O, hO⟩, hsub⟩⟩, ?_⟩
    obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (X := (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj dglob.U)) O).ge hwO
    refine ⟨y, ?_⟩
    have hmap : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
          (openChartInclusion B S hS X.1 dglob.U O ≫ WtoU)) =
        Scheme.Opens.ι O ≫
          (BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimage p) := by
      rw [Functor.map_comp, Functor.map_comp,
        toScheme_map_toOver_map_openChartInclusion B S hS X.1 dglob.U O]
      rfl
    rw [hmap]
    change ((BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimage p))
      ((Scheme.Opens.ι O) y) = x
    rw [hy]
    exact hw
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS X _ n U W a hcov fun i => ?_
  set d := dglob.restrictOpens (i.2.1 : _) (i.1 : _) i.2.2
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) :=
    inferInstanceAs (IsAffine ((i.1 : _) : Scheme))
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) :=
    inferInstanceAs (IsAffine ((i.2.1 : _) : Scheme))
  have hkey := definingIdealAt_preimage_eq_map B S hS (𝟙 X) ⟨R, hR.1⟩ d.V d.U d.g d.comm.symm
  have hV : definingIdealAt B S hS X ⟨R, hR.1⟩ (op d.V) ^ (n + 1) = ⊥ := by
    refine Ideal.pow_eq_bot_of_forall_isNilpotent
      (A := ((BigFppfOver.toScheme B S hS).obj d.V.1.left).presheaf.obj (op ⊤))
      (fun a ha => isNilpotent_of_mem_definingIdealAt_of_isThickening B S hS hR d.V hVa a ha) ?_
    refine nilradical_pow_eq_bot_of_ringEquiv
      ((i.1 : _).1.topIso.symm.commRingCatIsoToRingEquiv) ?_
    have h := congrArg (fun I => Scheme.IdealSheafData.ideal I i.1) hn
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at h
    exact h
  change definingIdealAt B S hS X ⟨R, hR.1⟩ (op d.U) ^ (n + 1) = ⊥
  rw [show (⟨R, hR.1⟩ : ClosedSubspaces B S hS X.1) =
    ⟨R.preimage (𝟙 X : X ⟶ X).hom,
      isClosedSubspace_preimage B S hS (𝟙 X : X ⟶ X).hom R X.2 X.2 hR.1⟩ from rfl, hkey]
  exact map_pow_eq_bot ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom hV

/-- **A thickening of an algebraic space with a surjective étale chart by a Noetherian scheme is
a finite order thickening.** -/
theorem isFiniteOrderThickening_of_atlas {X : AlgebraicSpaces B S hS} {R : Subfunctor X.1}
    (hR : IsThickening B S hS X R) (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ X.1)
    (hbS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b)
    (hbE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b)
    [IsNoetherian ((BigFppfOver.toScheme B S hS).obj V)] :
    IsFiniteOrderThickening B S hS X R :=
  let ⟨n, hn0, hn⟩ := Stacks.Divisors.exists_nilradical_pow_eq_bot
    ((BigFppfOver.toScheme B S hS).obj V)
  ⟨n - 1, isNthOrderThickening_of_atlas B S hS hR V b hbS hbE (by rwa [Nat.sub_add_cancel hn0])⟩

end Space

end AlgebraicGeometry
