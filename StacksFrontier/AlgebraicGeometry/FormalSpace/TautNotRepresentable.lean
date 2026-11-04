module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentableBoundedStages
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoffSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.Topology.Algebra.AdicTopology.TautUnboundedStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages
import all StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange

/-!
# Over a site with singular cutoff, a taut homomorphism need not give a representable morphism

Stacks 0AN5 states that for a continuous homomorphism `φ : A → C` of weakly admissible
topological rings over a scheme `S` the conditions (1) `Spf φ` is representable by algebraic
spaces, (2) `Spf φ` is representable, (3) `φ` is taut, are equivalent. In this library the
arrows (2) ⟹ (1), (1) ⟹ (3) and (2) ⟹ (3) hold over every big fppf site, and (3) ⟹ (2) holds
over a site whose size cutoff is a regular cardinal
(`AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_cutoff_isRegular`) and for a countably
indexed target over any site
(`AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_isCountablyGenerated`). This file shows
that the regularity of the cutoff cannot be dropped: over a site whose cutoff is singular,
(3) ⟹ (2) is false, and such sites exist. So the tag is false as stated for some big fppf sites,
and holds for all weakly admissible rings over a site exactly when its cutoff is regular.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isTaut_not_relativelyRepresentable_of_cof_lt`: over a
  site with singular cutoff there is a taut `φ` with `Spf φ` not representable.
* `AlgebraicGeometry.FormalSpace.exists_not_tfae_formalSpectrumMap_of_cof_lt`: hence the three
  conditions are not equivalent for it.
* `AlgebraicGeometry.FormalSpace.forall_formalSpectrumMap_tfae_iff_cutoff_isRegular`: the
  three conditions are equivalent for every `φ` over a site if and only if its cutoff is
  regular.
* `AlgebraicGeometry.FormalSpace.exists_bigFppfSite_isTaut_not_relativelyRepresentable`: a site
  over which the tag fails, with cutoff `ℶ_{ω₁}`.

## The counterexample

Let `μ < κ` be the cofinality of the cutoff `κ`, let `ι` be the initial ordinal of `μ`, and
choose cardinals `ν γ < κ`, `γ ∈ ι`, cofinal in `κ`. The homomorphism `φ : A → C` is that of
`TopologicalRing.TautUnboundedStages.exists_isTaut_card_stage` for types `V γ` of cardinality
`ν γ`. Its stages are all in the site: the stage of `A` at `γ` has cardinality at most `μ`, and
the stage of `C` at `γ` is bounded by it together with the product of the `Fiber (V α)` for
`α ≤ γ`, fewer than `μ` cardinals below the strong limit `κ`. But the stage of `C` at `γ`
contains `V γ`, so the stages of `C` are not uniformly bounded.

The test object is the coproduct `T` of the stages `Spec (A ⧸ I γ)` of `Spf A`. It lies in the
site because one bound, `μ`, controls both its index type and its members
(`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`), and its representable
sheaf is the coproduct of theirs, so the stage inclusions assemble into a point
`T ⟶ Spf A`. If the base change of `Spf φ` along it were represented by an object `W` of the
site, then each stage `Spec (C ⧸ closure (I γ • C))` of `Spf C`, which maps compatibly to `Spf C`
and to `T`, would lift to `W`, by a monomorphism because the stage inclusion into `Spf C` is one
(`AlgebraicGeometry.FormalSpace.mono_formalSpectrumInclusion`). Monomorphisms bound sizes
(`AlgebraicGeometry.Scheme.size_le_of_mono`) by `max (2 ^ #W) (size W) < κ`, a single cardinal
below the cutoff, which bounds every `ν γ`: a contradiction with their cofinality.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal
open TopologicalRing.TautUnboundedStages

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The initial segments of the type of the ordinal of a cardinal `c > ℵ₀` have fewer than `c`
elements. -/
theorem mk_Iic_lt_of_aleph0_lt {c : Cardinal.{u}} (hc : ℵ₀ < c) (γ : c.ord.ToType) :
    #{α : c.ord.ToType // α ≤ γ} < c := by
  have hIio : #(Set.Iio γ) < c := by
    have := Cardinal.mk_Iio_lt γ (by simp)
    rwa [Cardinal.mk_ord_toType] at this
  change #(Set.Iic γ) < c
  rw [← Set.Iio_insert]
  exact Cardinal.mk_insert_le.trans_lt
    (Cardinal.add_lt_of_lt hc.le hIio (Cardinal.one_lt_aleph0.trans hc))

/-- A product of fewer than `cof κ` types, each smaller than a strong limit `κ`, is smaller
than `κ`. -/
theorem mk_pi_lt_of_isStrongPrelimit {κ : Cardinal.{u}} (hκ : Cardinal.IsStrongPrelimit κ)
    (hℵ : ℵ₀ < κ) {β : Type u} (hβ : #β < κ.ord.cof) {F : β → Type u} (hF : ∀ b, #(F b) < κ) :
    #(∀ b, F b) < κ := by
  set M := ⨆ b, #(F b)
  set N := max (max M #β) ℵ₀
  have hN0 : ℵ₀ ≤ N := le_max_right _ _
  calc #(∀ b, F b) = Cardinal.prod fun b => #(F b) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : β => N := Cardinal.prod_le_prod _ _ fun b =>
        (le_ciSup (f := fun b => #(F b)) Cardinal.bddAbove_of_small b).trans
          ((le_max_left _ _).trans (le_max_left _ _))
    _ = N ^ #β := Cardinal.prod_const' _ _
    _ ≤ N ^ N := Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hN0).ne'
        ((le_max_right _ _).trans (le_max_left _ _))
    _ = 2 ^ N := Cardinal.power_self_eq hN0
    _ < κ := hκ (max_lt (max_lt (Cardinal.iSup_lt_of_lt_cof_ord hβ hF)
        (hβ.trans_le (Ordinal.cof_ord_le κ))) hℵ)

/-- The spectrum of `ℤ`, placed in universe `u`, has size at most `ℵ₀`. -/
theorem size_Spec_uliftInt_le : (Spec (CommRingCat.of (ULift.{u} ℤ))).size ≤ ℵ₀ := by
  rw [Scheme.size_Spec]
  exact max_le le_rfl Cardinal.mk_le_aleph0

variable (B : BigFppfSite.{u})

/-- The spectrum of a quotient of `R` lies in the site once a coarser quotient of `R` is smaller
than the cutoff. -/
theorem contains_spec_quotient_of_le {R : Type u} [CommRing R] {J J' : Ideal R} (h : J' ≤ J)
    (hc : #(R ⧸ J') < B.cutoff) : B.Contains (Spec (CommRingCat.of (R ⧸ J))) := by
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff
    ((Cardinal.mk_le_of_surjective (Ideal.Quotient.factor_surjective h)).trans_lt hc)

/-- A family of stages of `Spf A`, indexed by a type and of sizes bounded by a cardinal below the
cutoff, factors compatibly through the sheaf represented by a single object of the site. -/
theorem exists_sheafifiedYoneda_comp_eq_formalSpectrumInclusion {S : Scheme.{u}}
    {hS : B.Contains S} {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A) {ι : Type u}
    (I : ι → { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }) {μ : Cardinal.{u}}
    (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hI : ∀ γ, (Spec (CommRingCat.of (A ⧸ (I γ).1))).size ≤ μ) :
    ∃ (T : BigFppfOver B S hS)
      (j : ∀ γ, (BigAffineFppf.inclusion B S hS).obj (D.stage (I γ)) ⟶ T)
      (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ formalSpectrum D),
      ∀ γ, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (j γ) ≫ g =
        formalSpectrumInclusion D (OrderDual.toDual (I γ)) := by
  let X : ι → BigFppfOver B S hS := fun γ => (BigAffineFppf.inclusion B S hS).obj (D.stage (I γ))
  obtain ⟨T, j, -, -, -, -, ⟨hcol⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hI
  let Ψ := Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)
  let g' := Cofan.IsColimit.desc hcol fun γ =>
    Ψ.inv.app (X γ) ≫ formalSpectrumInclusion D (OrderDual.toDual (I γ))
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let g : G.obj T ⟶ formalSpectrum D := Ψ.hom.app T ≫ g'
  refine ⟨T, j, g, fun γ => ?_⟩
  have hn : G.map (j γ) ≫ Ψ.hom.app T =
      Ψ.hom.app (X γ) ≫ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j γ) :=
    Ψ.hom.naturality (j γ)
  have hf : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j γ) ≫ g' =
      Ψ.inv.app (X γ) ≫ formalSpectrumInclusion D (OrderDual.toDual (I γ)) :=
    Cofan.IsColimit.fac hcol _ γ
  change G.map (j γ) ≫ Ψ.hom.app T ≫ g' = _
  rw [← Category.assoc, hn, Category.assoc, hf]
  exact Iso.hom_inv_id_app_assoc Ψ (X γ) _

/-- If the base change of `Spf φ` along a point `T ⟶ Spf A` through which a stage of `Spf A`
factors is represented by an object `a` of the site, then the corresponding stage of `Spf C`
embeds into `a`, so its quotient ring has at most `max (2 ^ #a) (size a)` elements. -/
theorem card_quotient_closure_le_of_isPullback {S : Scheme.{u}} {hS : B.Contains S}
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    {hA : TopologicalRing.IsWeaklyAdmissible A} (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} {f : ContinuousHom D E}
    (htaut : RingHom.IsTaut f.toRingHom) {T a : BigFppfOver B S hS}
    {g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ formalSpectrum D}
    {snd : a ⟶ T}
    {fst : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ formalSpectrum E}
    (hpb : IsPullback fst ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map snd)
      (formalSpectrumMap hA f) g)
    (J : { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J })
    {j : (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶ T}
    (hj : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j ≫ g =
      formalSpectrumInclusion D (OrderDual.toDual J)) :
    #(C ⧸ (J.1.map f.toRingHom).closure) ≤
      max (2 ^ #((BigFppfOver.toScheme B S hS).obj a))
        ((BigFppfOver.toScheme B S hS).obj a).size := by
  obtain ⟨K, hK, hIK, -⟩ := isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f htaut J
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let u := formalSpectrumInclusion E (OrderDual.toDual K)
  have w : u ≫ formalSpectrumMap hA f =
      G.map ((BigAffineFppf.inclusion B S hS).map (f.stageMap J K hIK) ≫ j) ≫ g := by
    rw [formalSpectrumMap_spec hA f J K hIK, G.map_comp, Category.assoc, hj]
    rfl
  have hu : Mono u := formalSpectrumInclusion_mono B S hS hC.1 E _
  have : Mono (hpb.lift u _ w) := @mono_of_mono_fac _ _ _ _ _ _ _ _ hu (hpb.lift_fst u _ w)
  let m := (sheafifiedYonedaFF B S hS).preimage (hpb.lift u _ w)
  have : Mono m := by
    have := (sheafifiedYonedaFF B S hS).faithful
    refine G.mono_of_mono_map ?_
    rw [(sheafifiedYonedaFF B S hS).map_preimage]
    infer_instance
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp only [BigFppfOver.toScheme]
    infer_instance
  refine le_trans ?_ (Scheme.size_le_of_mono ((BigFppfOver.toScheme B S hS).map m))
  change #(C ⧸ (J.1.map f.toRingHom).closure) ≤ (Spec (CommRingCat.of (C ⧸ K.1))).size
  rw [Scheme.size_Spec, hK]
  exact le_max_right _ _

/-- **Stacks 0AN5 fails over a site whose cutoff is singular.** Over a big fppf site whose size
cutoff is a singular cardinal there are a scheme `S` of the site and a taut continuous
homomorphism `φ : A ⟶ C` of weakly admissible topological rings over `S` such that `Spf φ` is
not representable by objects of the site; so condition (3) of Stacks 0AN5 holds while (2) does
not, and the three conditions are not equivalent. -/
theorem exists_isTaut_not_relativelyRepresentable_of_cof_lt
    (hsing : B.cutoff.ord.cof < B.cutoff) :
    ∃ (S : Scheme.{u}) (hS : B.Contains S) (A : Type u) (_ : CommRing A)
      (_ : TopologicalSpace A) (_ : IsTopologicalRing A) (_ : IsLinearTopology A A)
      (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (hA : TopologicalRing.IsWeaklyAdmissible A)
      (_ : TopologicalRing.IsWeaklyAdmissible C) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS C) (f : ContinuousHom D E),
      RingHom.IsTaut f.toRingHom ∧
        ¬ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f) := by
  classical
  set c := B.cutoff.ord.cof
  have hℵc : ℵ₀ < c := B.aleph0_lt_cutoff_cof
  let ι := c.ord.ToType
  have hι : #ι = c := Cardinal.mk_ord_toType c
  have : Nonempty ι := Cardinal.mk_ne_zero_iff.1 (hι ▸ (Cardinal.aleph0_pos.trans hℵc).ne')
  obtain ⟨I, ν, hI, hν, hcof⟩ :=
    Cardinal.exists_cofinal_family_mk_eq_cof B.cutoff_isStrongPrelimit.isSuccPrelimit
  obtain ⟨e⟩ : Nonempty (ι ≃ I) := Cardinal.eq.1 (by rw [hι, hI])
  let V : ι → Type u := fun γ => (ν (e γ)).out
  have hV : ∀ γ, #(V γ) = ν (e γ) := fun γ => Cardinal.mk_out _
  obtain ⟨A, _, _, _, _, C, _, _, _, _, φ, Iγ, hA, hC, hφc, htaut, hI, hIopen, hAle, hKopen,
    hVle, hCle⟩ := exists_isTaut_card_stage ι V
  have hμ : max #ι ℵ₀ < B.cutoff := max_lt (hι.trans_lt hsing) B.aleph0_lt_cutoff
  have hstage : ∀ γ, #(Stage ι γ) < B.cutoff := fun γ => (card_stage_le ι γ).trans_lt hμ
  have hCγ : ∀ γ, #(C ⧸ ((Iγ γ).map φ).closure) < B.cutoff := fun γ =>
    (hCle γ).trans_lt (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le (hstage γ)
      (mk_pi_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit B.aleph0_lt_cutoff
        (mk_Iic_lt_of_aleph0_lt hℵc γ) fun α => (card_fiber_le (V α)).trans_lt
          (max_lt ((hV α).trans_lt (hν _)) B.aleph0_lt_cutoff)))
  let S : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))
  have hS : B.Contains S := size_Spec_uliftInt_le.trans_lt B.aleph0_lt_cutoff
  let D : QuotientSystem B S hS A :=
    { inSite := fun J => by
        obtain ⟨γ, hγ⟩ := hIopen J.1 J.2.1
        exact contains_spec_quotient_of_le B hγ ((hAle γ).trans_lt (hstage γ))
      overS := fun _ => specULiftZIsTerminal.from _
      compatible := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  let E : QuotientSystem B S hS C :=
    { inSite := fun K => by
        obtain ⟨γ, hγ⟩ := hKopen K.1 K.2.1
        exact contains_spec_quotient_of_le B hγ (hCγ γ)
      overS := fun _ => specULiftZIsTerminal.from _
      compatible := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  let f : ContinuousHom D E := ⟨φ, hφc, fun _ _ _ => specULiftZIsTerminal.hom_ext _ _⟩
  refine ⟨S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f, htaut, fun hrep => ?_⟩
  let Iw : ι → { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J } :=
    fun γ => ⟨Iγ γ, hI γ⟩
  obtain ⟨T, j, g, hg⟩ := exists_sheafifiedYoneda_comp_eq_formalSpectrumInclusion B D Iw hμ
    (le_max_left _ _) fun γ => by
      rw [Scheme.size_Spec]
      exact max_le (le_max_right _ _) ((hAle γ).trans (card_stage_le ι γ))
  obtain ⟨a, snd, fst, hpb⟩ := hrep g
  obtain ⟨i, hi⟩ := hcof _ (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit
    B.cutoff_isStrongPrelimit a.left.2)
  have := (hVle (e.symm i)).trans <| card_quotient_closure_le_of_isPullback B hC (f := f) htaut
    hpb (Iw (e.symm i)) (hg (e.symm i))
  rw [hV, Equiv.apply_symm_apply] at this
  exact not_le.2 hi this

/-- A taut `φ` with `Spf φ` not representable by objects of the site refutes the equivalence of
the three conditions of Stacks 0AN5. -/
private theorem not_tfae_of_isTaut_of_not_relativelyRepresentable {S : Scheme.{u}}
    {hS : B.Contains S} {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] {hA : TopologicalRing.IsWeaklyAdmissible A}
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} {f : ContinuousHom D E}
    (htaut : RingHom.IsTaut f.toRingHom)
    (hnot : ¬ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap hA f)) :
    ¬ List.TFAE
      [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f),
        RingHom.IsTaut f.toRingHom] :=
  fun h => hnot ((h.out 3 2).mp htaut)

/-- **The three conditions of Stacks 0AN5 are not equivalent over a site with singular
cutoff.** Over a big fppf site whose size cutoff is singular there are a scheme `S` of the site
and a continuous homomorphism `φ : A ⟶ C` of weakly admissible topological rings over `S` for
which the conditions

1. `Spf φ` is representable by algebraic spaces over `S`,
2. `Spf φ` is representable by objects of the site,
3. `φ` is taut

are not equivalent: (3) holds and (2) fails, by
`AlgebraicGeometry.FormalSpace.exists_isTaut_not_relativelyRepresentable_of_cof_lt`. -/
theorem exists_not_tfae_formalSpectrumMap_of_cof_lt (hsing : B.cutoff.ord.cof < B.cutoff) :
    ∃ (S : Scheme.{u}) (hS : B.Contains S) (A : Type u) (_ : CommRing A)
      (_ : TopologicalSpace A) (_ : IsTopologicalRing A) (_ : IsLinearTopology A A)
      (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (hA : TopologicalRing.IsWeaklyAdmissible A)
      (_ : TopologicalRing.IsWeaklyAdmissible C) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS C) (f : ContinuousHom D E),
      ¬ List.TFAE
        [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
            (formalSpectrumMap hA f),
          RingHom.IsTaut f.toRingHom] := by
  obtain ⟨S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f, htaut, hnot⟩ :=
    exists_isTaut_not_relativelyRepresentable_of_cof_lt B hsing
  exact ⟨S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f,
    not_tfae_of_isTaut_of_not_relativelyRepresentable B htaut hnot⟩

/-- **Stacks 0AN5 holds over a big fppf site exactly when its cutoff is regular.** For a big fppf
site `B` the following are equivalent:

* for every scheme `S` of the site and every continuous homomorphism `φ : A ⟶ C` of weakly
  admissible topological rings over `S`, the three conditions of Stacks 0AN5 — `Spf φ`
  representable by algebraic spaces, `Spf φ` representable by objects of the site, `φ` taut —
  are equivalent;
* the size cutoff of `B` is a regular cardinal.

Backwards this is `AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_cutoff_isRegular`.
Forwards, a cutoff which is not regular has cofinality below it, and then
`AlgebraicGeometry.FormalSpace.exists_not_tfae_formalSpectrumMap_of_cof_lt` produces a taut
homomorphism for which the equivalence fails. -/
@[stacks 0AN5 "the equivalence of (1), (2) and (3) for all weakly admissible rings holds over \
a site exactly when its cutoff is a regular cardinal"]
theorem forall_formalSpectrumMap_tfae_iff_cutoff_isRegular :
    (∀ (S : Scheme.{u}) (hS : B.Contains S) (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLinearTopology A A] (C : Type u) [CommRing C]
      [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      (hA : TopologicalRing.IsWeaklyAdmissible A) (_ : TopologicalRing.IsWeaklyAdmissible C)
      (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E),
      List.TFAE
        [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
            (formalSpectrumMap hA f),
          RingHom.IsTaut f.toRingHom]) ↔ B.cutoff.IsRegular := by
  refine ⟨fun h => ⟨B.aleph0_lt_cutoff.le, ?_⟩, fun hreg S hS A _ _ _ _ C _ _ _ _ hA hC D E f =>
    formalSpectrumMap_tfae_of_cutoff_isRegular B S hS hA hC D E f hreg⟩
  by_contra hle
  obtain ⟨S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f, hnot⟩ :=
    exists_not_tfae_formalSpectrumMap_of_cof_lt B (not_le.1 hle)
  exact hnot (h S hS A C hA hC D E f)

/-- **Stacks 0AN5 is false as stated for some big fppf site.** There are a big fppf site, a
scheme `S` of it, and a continuous homomorphism `φ : A ⟶ C` of weakly admissible topological
rings over `S` which is taut while `Spf φ` is not representable by objects of the site; so the
three conditions of Stacks 0AN5 are not equivalent for it.

The site is the one of `AlgebraicGeometry.BigFppfSite.exists_cutoff_eq` with cutoff
`AlgebraicGeometry.singularCutoff = ℶ_{ω₁}`, a singular cardinal satisfying every cardinal axiom
of `AlgebraicGeometry.BigFppfSite`, and the homomorphism is the one of
`AlgebraicGeometry.FormalSpace.exists_isTaut_not_relativelyRepresentable_of_cof_lt`. The
statement holds, in the form of all three equivalences, over a site whose cutoff is regular
(`AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_cutoff_isRegular`) and for a
countably indexed target over any site
(`AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_isCountablyGenerated`). -/
@[stacks 0AN5 "false as stated over a site whose cutoff is singular: (3) does not imply (2)"]
theorem exists_bigFppfSite_isTaut_not_relativelyRepresentable :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (A : Type u) (_ : CommRing A)
      (_ : TopologicalSpace A) (_ : IsTopologicalRing A) (_ : IsLinearTopology A A)
      (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (hA : TopologicalRing.IsWeaklyAdmissible A)
      (_ : TopologicalRing.IsWeaklyAdmissible C) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS C) (f : ContinuousHom D E),
      RingHom.IsTaut f.toRingHom ∧
        ¬ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f) ∧
        ¬ List.TFAE
          [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
              (formalSpectrumMap hA f).hom,
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
              (formalSpectrumMap hA f),
            RingHom.IsTaut f.toRingHom] := by
  obtain ⟨B, hcut, -⟩ := BigFppfSite.exists_cutoff_eq singularCutoff.{u}
    aleph0_lt_singularCutoff isStrongPrelimit_singularCutoff
    (cof_ord_singularCutoff.{u} ▸ Cardinal.aleph0_lt_aleph_one)
    {Spec (CommRingCat.of (ULift.{u} ℤ))} (by
      rintro X rfl
      exact size_Spec_uliftInt_le.trans_lt aleph0_lt_singularCutoff)
  have hsing : B.cutoff.ord.cof < B.cutoff := by
    rw [hcut, cof_ord_singularCutoff]
    exact aleph_one_lt_singularCutoff
  obtain ⟨S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f, htaut, hnot⟩ :=
    exists_isTaut_not_relativelyRepresentable_of_cof_lt B hsing
  exact ⟨B, S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f, htaut, hnot,
    not_tfae_of_isTaut_of_not_relativelyRepresentable B htaut hnot⟩

end AlgebraicGeometry.FormalSpace

end
