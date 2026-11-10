module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.FlatIsLocal

/-!
# Rig-flatness is stable under composition

Stacks 0GGV asserts that rig-flatness of arrows of `WAdm^Noeth` (Stacks 0GGP) is stable under
composition in the sense of Remark 0GBK: it is a local property (Stacks 0GGU) and the composite
of two continuous rig-flat homomorphisms of Noetherian adic topological rings is rig-flat.

For the composition statement, adicness and topological finite type of the composite are the
corresponding fact for adic morphisms of topological finite type (Stacks 0GBZ). What remains is
naive rig-flatness of the induced map of completed principal localizations. Naive rig-flatness
is itself stable under composition — the flatness condition
`(A ⧸ nothing) → B[1/φ(x)] → C[1/ψφ(x)]` factors through the localization of `B` at `φ(x)`, over
which the final localization is flat by Stacks 00HT (2) — and the induced map of completed
principal localizations of the composite is the composite of the induced maps, up to the
identification of the two ways of extending the ideal to the final localization. That
functoriality is `Rig.completedAwayMap_comp`.

## Main definitions

* `Rig.adicCompletionCongrOfEq`: the isomorphism of adic completions along two equal ideals,
  built as the map induced by the identity rather than by transport along the equality, so that
  its evaluations are computed by `adicCompletionMap_evalₐ`.

## Main results

* `Rig.rigFlat_isStableUnderCompositionNoetherian`: **Stacks 0GGV**.
* `Rig.RingHom.isNaivelyRigFlat_comp`: naive rig-flatness is stable under composition.
* `Rig.completedAwayMap_comp`: the map of completed principal localizations is functorial.
* `Rig.RingHom.isNaivelyRigFlat_of_ringEquiv_isAdic`: an adic isomorphism of topological rings
  is naively rig-flat.

## Implementation notes

`Rig.adicCompletionCongrOfEq` is deliberately *not* defined by transporting
`RingEquiv.refl` along the equality of ideals: that definition makes the proof term of
`Rig.completedAwayMap_comp` carry an `Eq.rec` over an ideal of a localization of a completion,
which the kernel does not check in reasonable time. Defining it as `Rig.adicCompletionCongr` of
the identity gives the same map with evaluations that reduce.

## References

* [Stacks Project, Tag 0GGV](https://stacks.math.columbia.edu/tag/0GGV)
* [Stacks Project, Tag 0GGU](https://stacks.math.columbia.edu/tag/0GGU)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBZ](https://stacks.math.columbia.edu/tag/0GBZ)
-/

@[expose] public section

open TopologicalRing

universe u

namespace Rig

namespace RingHom

/-- Naive rig-flatness is stable under composition: the flatness condition for the composite at
a topologically nilpotent element follows from that for the two factors, because the
localization of the final ring is flat over the localization of the middle ring. -/
theorem isNaivelyRigFlat_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
    (f : A →+* B) (g : B →+* C) (hf_cont : Continuous f) (hg_cont : Continuous g)
    (hf : IsNaivelyRigFlat f) (hg : IsNaivelyRigFlat g) :
    IsNaivelyRigFlat (g.comp f) := by
  obtain ⟨hf_adic, hf_tft, hf_flat⟩ := hf
  obtain ⟨hg_adic, hg_tft, hg_flat⟩ := hg
  refine ⟨_root_.RingHom.isAdic_comp f g hf_adic hg_adic,
    TopologicalRing.isTopologicallyOfFiniteType_comp g f hg_cont hg_tft hf_tft, ?_⟩
  intro a ha
  let Bₚ := Localization.Away (f a)
  let Cₚ := Localization.Away (g (f a))
  let q : B →+* Cₚ := (algebraMap C Cₚ).comp g
  let k : Bₚ →+* Cₚ := IsLocalization.Away.map Bₚ Cₚ g (f a)
  have hk : k.comp (algebraMap B Bₚ) = q := by
    ext x
    simp [k, q, Bₚ, Cₚ, IsLocalization.Away.map, RingHom.comp_apply]
  let : Algebra Bₚ Cₚ := k.toAlgebra
  let : Algebra B Cₚ := q.toAlgebra
  let : IsScalarTower B Bₚ Cₚ := IsScalarTower.of_algebraMap_eq' hk.symm
  have hBflat : Module.Flat B Cₚ := hg_flat (f a) (IsTopologicallyNilpotent.map hf_cont ha)
  have hBₚflat : Module.Flat Bₚ Cₚ :=
    (flat_iff_flat_localization (Submonoid.powers (f a)) Bₚ Cₚ).mp hBflat
  have hcomp : _root_.RingHom.Flat ((algebraMap Bₚ Cₚ).comp
      ((algebraMap B Bₚ).comp f)) :=
    _root_.RingHom.Flat.comp (hf_flat a ha)
      (show _root_.RingHom.Flat (algebraMap Bₚ Cₚ) from hBₚflat)
  have hmap : (algebraMap Bₚ Cₚ).comp ((algebraMap B Bₚ).comp f) =
      (algebraMap C Cₚ).comp (g.comp f) := by
    ext x
    exact DFunLike.congr_fun hk (f x)
  rwa [hmap] at hcomp

end RingHom

/-- The isomorphism of adic completions along two equal ideals, as the map induced by the
identity. -/
noncomputable def adicCompletionCongrOfEq {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I = J) : AdicCompletion I R ≃+* AdicCompletion J R :=
  adicCompletionCongr (RingEquiv.refl R) I J (by simpa using h)

/-- `Rig.adicCompletionCongrOfEq` is the identity on evaluations. -/
theorem evalₐ_adicCompletionCongrOfEq {R : Type*} [CommRing R]
    {I J : Ideal R} (h : I = J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicCompletionCongrOfEq h x) =
      Ideal.quotientMap (J ^ n) (RingEquiv.refl R).toRingHom
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact pow_le_pow_left' (by simpa using h.le) n))
        (AdicCompletion.evalₐ I n x) :=
  adicCompletionMap_evalₐ (RingEquiv.refl R).toRingHom I J (by simpa using h.le) n x

/-- `Rig.adicCompletionCongrOfEq` commutes with the structure maps. -/
theorem adicCompletionCongrOfEq_comp_algebraMap
    {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    (adicCompletionCongrOfEq h).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      algebraMap R (AdicCompletion J R) := by
  refine RingHom.ext fun x ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_
  change AdicCompletion.evalₐ J n (adicCompletionCongrOfEq h
    (algebraMap R (AdicCompletion I R) x)) = _
  rw [evalₐ_adicCompletionCongrOfEq]
  simp [AdicCompletion.algebraMap_apply]

namespace RingHom

/-- An adic isomorphism of topological rings is naively rig-flat. -/
theorem isNaivelyRigFlat_of_ringEquiv_isAdic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃+* B) (he : _root_.RingHom.IsAdic e.toRingHom) :
    IsNaivelyRigFlat e.toRingHom := by
  refine ⟨he, ⟨0, MvPolynomial.eval₂Hom e.toRingHom (fun i ↦ Fin.elim0 i), ?_, ?_⟩, ?_⟩
  · ext x
    simp
  · rw [denseRange_iff_closure_range,
      show Set.range (MvPolynomial.eval₂Hom e.toRingHom (fun i : Fin 0 ↦ Fin.elim0 i)) =
        Set.univ from Set.range_eq_univ.mpr fun y ↦ ⟨MvPolynomial.C (e.symm y), by simp⟩]
    exact isClosed_univ.closure_eq
  · intro x _
    exact _root_.RingHom.Flat.comp (_root_.RingHom.Flat.of_bijective e.bijective)
      (_root_.RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away (e.toRingHom x))
          (Submonoid.powers (e.toRingHom x))))

end RingHom

/-- Extending an ideal to a principal localization of the final ring does not see the
intermediate ring: the composite extension and the two-step extension agree. -/
theorem map_map_algebraMap_localizationAway_eq {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) (I : Ideal A) (a : A) :
    ((I.map f).map g).map (algebraMap C (Localization.Away (g (f a)))) =
      (I.map (g.comp f)).map (algebraMap C (Localization.Away (g (f a)))) := by
  simp only [Ideal.map_map]

/-- The maps of principal localizations compose. -/
theorem localizationAwayMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (a : A) :
    (IsLocalization.Away.map (Localization.Away (f a)) (Localization.Away (g (f a))) g
          (f a)).comp
        (IsLocalization.Away.map (Localization.Away a) (Localization.Away (f a)) f a) =
      IsLocalization.Away.map (Localization.Away a) (Localization.Away (g (f a)))
        (g.comp f) a := by
  refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun z ↦ ?_)
  simp only [RingHom.comp_apply, IsLocalization.Away.map, IsLocalization.map_eq]

/-- **The map of completed principal localizations is functorial.** The composite of the maps
induced by `f` and by `g` is the map induced by `g ∘ f`, through the identification
`Rig.adicCompletionCongrOfEq` of the two extensions of the ideal. -/
theorem completedAwayMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (I : Ideal A) (a : A) :
    (adicCompletionCongrOfEq
          (map_map_algebraMap_localizationAway_eq f g I a)).toRingHom.comp
        ((RingHom.completedAwayMap g (I.map f) (f a)).comp
          (RingHom.completedAwayMap f I a)) =
      RingHom.completedAwayMap (g.comp f) I a := by
  refine RingHom.ext fun x ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_
  let L := Localization.Away a
  let M := Localization.Away (f a)
  let T := Localization.Away (g (f a))
  let φ : L →+* M := IsLocalization.Away.map L M f a
  let ψ : M →+* T := IsLocalization.Away.map M T g (f a)
  let χ : L →+* T := IsLocalization.Away.map L T (g.comp f) a
  let : Algebra L M := φ.toAlgebra
  let : Algebra M T := ψ.toAlgebra
  let : Algebra L T := χ.toAlgebra
  have hlocal : ψ.comp φ = χ := localizationAwayMap_comp f g a
  change AdicCompletion.evalₐ _ n (adicCompletionCongrOfEq
      (map_map_algebraMap_localizationAway_eq f g I a)
      ((RingHom.completedAwayMap g (I.map f) (f a))
        ((RingHom.completedAwayMap f I a) x))) = _
  rw [evalₐ_adicCompletionCongrOfEq]
  simp only [RingHom.completedAwayMap]
  refine Eq.trans ?_ (Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion
    (I := I.map (algebraMap A L)) _ n x).symm
  rw [Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion,
    Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (I.map (algebraMap A L)) n x)
  rw [← hy]
  exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun hlocal y)

/-- **Rig-flatness is stable under composition on `WAdm^Noeth`** (Stacks 0GGV). Adicness and
topological finite type of the composite are Stacks 0GBZ; naive rig-flatness of the induced map
of completed principal localizations is `Rig.RingHom.isNaivelyRigFlat_comp` applied to the two
factors, transported along the functoriality `Rig.completedAwayMap_comp`. -/
@[stacks 0GGV]
theorem rigFlat_isStableUnderCompositionNoetherian :
    TopologicalRing.PropertyIsStableUnderCompositionNoetherian
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ) where
  isLocal := rigFlat_isLocalNoetherian
  comp := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC f g hf_cont hg_cont hf hg
    have : IsNoetherianRing A := hA.2
    have : IsNoetherianRing B := hB.2
    have : IsNoetherianRing C := hC.2
    have hstable :=
      TopologicalRing.adicTopologicallyFiniteType_isStableUnderComposition.comp
        ⟨weaklyAdmissible_of_isAdicRing hA.1, countablyGenerated_nhds_of_isAdicRing hA.1⟩
        ⟨weaklyAdmissible_of_isAdicRing hB.1, countablyGenerated_nhds_of_isAdicRing hB.1⟩
        ⟨weaklyAdmissible_of_isAdicRing hC.1, countablyGenerated_nhds_of_isAdicRing hC.1⟩
        (exists_fg_isAdic_of_isAdicRing hA.1) (exists_fg_isAdic_of_isAdicRing hB.1)
        (exists_fg_isAdic_of_isAdicRing hC.1) f g hf_cont hg_cont
        ⟨hf.1, hf.2.1⟩ ⟨hg.1, hg.2.1⟩
    obtain ⟨hf_adic, hf_tft, hf_rig⟩ := hf
    obtain ⟨hg_adic, hg_tft, hg_rig⟩ := hg
    refine ⟨hstable.1, hstable.2, ?_⟩
    intro I hI
    rw [forall_comm]
    intro a hIA
    let C_f := Localization.Away a
    let B_f := Localization.Away (g a)
    let A_f := Localization.Away (f (g a))
    let I_f := I.map (algebraMap C C_f)
    let J_f := (I.map g).map (algebraMap B B_f)
    let K_f := ((I.map g).map f).map (algebraMap A A_f)
    let K₂_f := (I.map (f.comp g)).map (algebraMap A A_f)
    let I_hat := I_f.map (algebraMap C_f (AdicCompletion I_f C_f))
    let J_hat := J_f.map (algebraMap B_f (AdicCompletion J_f B_f))
    let K_hat := K_f.map (algebraMap A_f (AdicCompletion K_f A_f))
    let K₂_hat := K₂_f.map (algebraMap A_f (AdicCompletion K₂_f A_f))
    let : TopologicalSpace (AdicCompletion I_f C_f) := I_hat.adicTopology
    let : TopologicalSpace (AdicCompletion J_f B_f) := J_hat.adicTopology
    let : TopologicalSpace (AdicCompletion K_f A_f) := K_hat.adicTopology
    let : TopologicalSpace (AdicCompletion K₂_f A_f) := K₂_hat.adicTopology
    let : IsTopologicalRing (AdicCompletion I_f C_f) :=
      I_hat.nonarchimedean.toIsTopologicalRing
    let : IsTopologicalRing (AdicCompletion J_f B_f) :=
      J_hat.nonarchimedean.toIsTopologicalRing
    let : IsTopologicalRing (AdicCompletion K_f A_f) :=
      K_hat.nonarchimedean.toIsTopologicalRing
    let : IsTopologicalRing (AdicCompletion K₂_f A_f) :=
      K₂_hat.nonarchimedean.toIsTopologicalRing
    have hIB : _root_.IsAdic (I.map g) := _root_.RingHom.isAdic_map_of_isAdic g hg_adic hI
    have hIC : _root_.IsAdic ((I.map g).map f) := by
      rw [Ideal.map_map]
      exact hIA
    have hq := hg_rig I hI hIB a
    have hp := hf_rig (I.map g) hIB hIC (g a)
    have hcomp := RingHom.isNaivelyRigFlat_comp
      (RingHom.completedAwayMap g I a) (RingHom.completedAwayMap f (I.map g) (g a))
      (RingHom.continuous_of_isAdic _ hq.1) (RingHom.continuous_of_isAdic _ hp.1) hq hp
    have hJ : K_f = K₂_f := map_map_algebraMap_localizationAway_eq g f I a
    have heMap : K_hat.map (adicCompletionCongrOfEq hJ).toRingHom = K₂_hat :=
      calc K_hat.map (adicCompletionCongrOfEq hJ).toRingHom
          = K_f.map ((adicCompletionCongrOfEq hJ).toRingHom.comp
              (algebraMap A_f (AdicCompletion K_f A_f))) := Ideal.map_map _ _
        _ = K_f.map (algebraMap A_f (AdicCompletion K₂_f A_f)) :=
              congrArg K_f.map (adicCompletionCongrOfEq_comp_algebraMap hJ)
        _ = K₂_hat :=
              congrArg
                (fun K : Ideal A_f ↦ K.map (algebraMap A_f (AdicCompletion K₂_f A_f))) hJ
    have he_adic : _root_.RingHom.IsAdic (adicCompletionCongrOfEq hJ).toRingHom :=
      ⟨K_hat, rfl, congrArg Ideal.adicTopology heMap.symm⟩
    have he_naive := RingHom.isNaivelyRigFlat_of_ringEquiv_isAdic _ he_adic
    have htransport := RingHom.isNaivelyRigFlat_comp
      ((RingHom.completedAwayMap f (I.map g) (g a)).comp (RingHom.completedAwayMap g I a))
      (adicCompletionCongrOfEq hJ).toRingHom
      (RingHom.continuous_of_isAdic _ hcomp.1)
      (RingHom.continuous_of_isAdic _ he_adic) hcomp he_naive
    rw [completedAwayMap_comp] at htransport
    exact htransport

end Rig

end
