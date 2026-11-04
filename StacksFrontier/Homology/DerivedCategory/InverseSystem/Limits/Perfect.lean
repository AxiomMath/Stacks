module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.Local

open StacksDraft.DerivedInverseLimit

/-!
# Perfectness of a derived inverse limit

Let `(Aₙ)` be an inverse system of commutative rings with surjective transition maps whose
kernels are locally nilpotent, and let `(Kₙ)` be a compatible inverse system of objects of the
derived categories `D(Aₙ)` whose transition maps induce isomorphisms `Kₙ₊₁ ⊗ᴸ[Aₙ₊₁] Aₙ ≅ Kₙ`.
If every `Kₙ` is perfect, or one of them is and all subsequent transition kernels are nilpotent,
then a derived inverse limit of `(Kₙ)` over the limit ring is perfect, and its canonical derived
base-change map to each `Kₙ` is an isomorphism. When the limit ring is adically complete and the
tower is the tower of its quotients by the powers of the ideal, the derived inverse limit is
moreover derived complete.

## Main results

* `StacksDraft.DerivedInverseLimit.isPerfect_of_surjective_baseChange`: a pseudo-coherent object
  is perfect once its derived base change along a surjection detecting units is perfect.
* `StacksDraft.DerivedInverseLimit.derivedLimit_isPerfect_and_baseChange_iso`: perfectness of a
  derived inverse limit together with invertibility of all its canonical derived base-change maps.
* `StacksDraft.DerivedInverseLimit.derivedLimit_isPerfect_isDerivedComplete_and_baseChange_iso`:
  the adically complete case, where the derived inverse limit is in addition derived complete.

## Implementation notes

The rings lie in universe `u` and the modules in the universe `max u v`.

## References

* [Bhatt, *Completions and derived de Rham cohomology*, Lemma 4.2][Bhatt-Algebraize]
* [The Stacks Project, Tag 0CQG](https://stacks.math.columbia.edu/tag/0CQG)
* [The Stacks Project, Tag 09AW](https://stacks.math.columbia.edu/tag/09AW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace StacksDraft.DerivedInverseLimit

universe u v uR uS uT w

attribute [local instance] HasDerivedCategory.standard


/-! ### Perfectness of a derived inverse limit -/

private theorem isUnit_of_map_of_locallyNilpotent_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (x : R) (hx : IsUnit (f x)) : IsUnit x := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨y, hy⟩ := hf (↑z⁻¹)
  have hnil : IsNilpotent (1 - x * y) := hker _ (by
    rw [RingHom.mem_ker, map_sub, map_one, map_mul, hy, ← hz]
    simp)
  exact isUnit_of_mul_isUnit_left (by simpa only [sub_sub_cancel] using hnil.isUnit_one_sub)

private theorem isUnit_of_isUnit_limit_projection_zero
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (hs : ∀ n, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hn : ∀ n, (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom).IsLocallyNilpotent)
    (x : c.pt) (hx : IsUnit ((c.π.app (op 0)).hom x)) : IsUnit x := by
  apply (CommRingCat.Limits.isUnit_iff_forall_isUnit A hc x).2
  rintro ⟨n⟩
  induction n with
  | zero => exact hx
  | succ n ih =>
    apply isUnit_of_map_of_locallyNilpotent_ker _ (hs n) (hn n)
    have hw := congrArg (fun f : c.pt ⟶ A.obj (op n) => f.hom x)
      (c.w (homOfLE (Nat.le_succ n)).op)
    exact hw.symm ▸ ih

private noncomputable def derivedRestrictScalarsCompGeneral
    {R : Type uR} {S : Type uS} {T : Type uT}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (ModuleCat.restrictScalars.{max uR uS uT w} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max uR uS uT w} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{max uR uS uT w} (g.comp f)).mapDerivedCategory := by
  let F := ModuleCat.restrictScalars.{max uR uS uT w} g
  let G := ModuleCat.restrictScalars.{max uR uS uT w} f
  let H := ModuleCat.restrictScalars.{max uR uS uT w} (g.comp f)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uS uT w} T) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (DerivedCategory.Q ⋙ H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp f g).symm (ComplexShape.up ℤ)) _ ≪≫
      H.mapDerivedCategoryFactors.symm)

private noncomputable def derivedExtensionScalarsUniverseIso
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uS, w} f).functor ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uS, max uR uS w}
        f).functor := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uS, w} f
  let D' :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uS, max uR uS w} f
  exact Adjunction.leftAdjointUniq
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uS, w}
      R S _ _ f _ _ D.functor D.comparison D.isLeftDerived)
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uS, max uR uS w}
      R S _ _ f _ _ D'.functor D'.comparison D'.isLeftDerived)

private noncomputable def derivedExtensionScalarsComp
    {R : Type uR} {S : Type uS} {T : Type uT}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uS, max uR uS uT w}
      f).functor ⋙
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uS, uT, max uR uS uT w}
        g).functor ≅
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uT, max uR uS uT
          w} (g.comp f)).functor := by
  let Df :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uS, max uR uS uT w} f
  let Dg :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uS, uT, max uR uS uT w} g
  let Dh := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uT,
    max uR uS uT w} (g.comp f)
  let af := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uS,
    max uR uS uT w} R S _ _ f _ _ Df.functor Df.comparison Df.isLeftDerived
  let ag := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uS, uT,
    max uR uS uT w} S T _ _ g _ _ Dg.functor Dg.comparison Dg.isLeftDerived
  let ah := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uT,
    max uR uS uT w} R T _ _ (g.comp f) _ _ Dh.functor Dh.comparison Dh.isLeftDerived
  exact Adjunction.leftAdjointUniq
    ((af.comp ag).ofNatIsoRight (derivedRestrictScalarsCompGeneral.{uR, uS, uT, w} f g)) ah

private theorem derivedExtensionScalars_id_iso
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : PseudoCoherence.IsPseudoCoherent K) :
    Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
      (RingHom.id R)).functor.obj K ≅ K) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  have : ∀ i, Projective (P.X i) := fun i => by
    have := (hP.finiteFree i).2
    infer_instance
  let D :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)
  have := D.comparison_isIso_of_projective P b
  exact ⟨D.functor.mapIso e.symm ≪≫ asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, max u v} R)
        (ComplexShape.up ℤ)).app P ≪≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ)).app P) ≪≫ e⟩

private theorem ker_le_jacobson_of_isUnit_of_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : ∀ x, IsUnit (f x) → IsUnit x) :
    RingHom.ker f ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  refine Ideal.mem_jacobson_bot.mpr fun y => hf _ ?_
  simpa only [map_add, map_mul, RingHom.mem_ker.mp hx, zero_mul, map_one, zero_add]
    using isUnit_one

private theorem isPerfect_of_surjective_baseChange_largeSource
    {R : Type (max u v)} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hs : Function.Surjective f)
    (hu : ∀ x, IsUnit (f x) → IsUnit x)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : PseudoCoherence.IsPseudoCoherent K)
    (hperf : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{max u v, u, max u v}
        f).functor.obj K)) :
    StacksDraft.Perfect.IsPerfect K := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨e⟩⟩ := hperf
  have hc := StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes K hK a b
  apply (hc.1.mpr (hc.2.mpr ?_)).1
  intro m i hi
  have hker : RingHom.ker f ≤ RingHom.ker (algebraMap R m.asIdeal.ResidueField) := by
    rw [Ideal.ker_algebraMap_residueField]
    exact (ker_le_jacobson_of_isUnit_of_map f hu).trans
      (by rw [Ideal.jacobson_bot]; exact Ring.jacobson_le_of_isMaximal m.asIdeal)
  let g := f.liftOfSurjective hs ⟨algebraMap R m.asIdeal.ResidueField, hker⟩
  have hgf : g.comp f = algebraMap R m.asIdeal.ResidueField :=
    f.liftOfSurjective_comp hs _
  let F := ModuleCat.extendScalars.{u, max u v, max u v} g
  let D :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, max u v, max u v} g
  have : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj g).isLeftAdjoint
  have : ∀ j, Projective (P.X j) := fun j => by
    have := hproj j
    infer_instance
  have hcomparison : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  let ecomp := (derivedExtensionScalarsComp.{max u v, u, max u v, max u v} f g).app K
  let E : CochainComplex (ModuleCat.{max u v} m.asIdeal.ResidueField) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have he : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{max u v,
      max u v, max u v} (algebraMap R m.asIdeal.ResidueField)).functor.obj K ≅
        DerivedCategory.Q.obj E := by
    rw [← hgf]
    exact ecomp.symm ≪≫ D.functor.mapIso e ≪≫
      @asIso _ _ _ _ (D.comparison.app P) hcomparison
  have hzero : IsZero (E.homology i) := by
    rcases hi with hi | hi
    · have : E.IsStrictlyGE a := inferInstance
      exact E.isZero_of_isGE a i hi
    · have : E.IsStrictlyLE b := inferInstance
      exact E.isZero_of_isLE b i hi
  exact (StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology m.asIdeal K hK i).mpr <|
    hzero.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso he ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app E)

/-- **Perfectness descends along a surjection detecting units.** Let `f : R ⟶ S` be a surjective
ring homomorphism such that an element of `R` is a unit as soon as its image is, and let `K` be a
pseudo-coherent object of `D(R)`. If `S ⊗^𝐋_R K` is a perfect object of `D(S)`, then `K` is
perfect. The hypothesis `hu` holds exactly when the kernel of `f` is contained in the Jacobson
radical of `R`. -/
public theorem isPerfect_of_surjective_baseChange
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hs : Function.Surjective f)
    (hu : ∀ x, IsUnit (f x) → IsUnit x)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : PseudoCoherence.IsPseudoCoherent K)
    (hperf : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} f).functor.obj
        K)) :
    StacksDraft.Perfect.IsPerfect K := by
  let e := ULift.ringEquiv.{u, v} (R := R)
  let j := e.symm.toRingHom
  let f' := f.comp e.toRingHom
  let D :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, max u v, max u v} j
  let K' := D.functor.obj K
  have hK' : PseudoCoherence.IsPseudoCoherent K' :=
    (StacksDraft.PseudoCoherence.totalDerivedExtensionScalars_preserves_pseudoCoherent j K).2 hK
  have hf'j : f'.comp j = f := by ext x; simp [f', j, e]
  have hid : e.toRingHom.comp j = RingHom.id R := by ext x; simp [j, e]
  have hperf' : StacksDraft.Perfect.IsPerfect K' := by
    apply isPerfect_of_surjective_baseChange_largeSource f'
      (hs.comp e.surjective) (fun x hx => by
        simpa [e] using (hu _ hx).map e.symm) K' hK'
    have ei := (derivedExtensionScalarsComp.{u, max u v, u, v} j f').app K
    rw [hf'j] at ei
    exact StacksDraft.Perfect.isPerfect_of_iso
      (((derivedExtensionScalarsUniverseIso.{u, u, v} f).app K ≪≫ ei.symm).symm) hperf
  have hback := StacksDraft.Perfect.isPerfect_derivedExtensionScalars.{max u v, u, max u v}
    e.toRingHom K' hperf'
  have ei := (derivedExtensionScalarsComp.{u, max u v, u, v} j e.toRingHom).app K
  rw [hid] at ei
  exact StacksDraft.Perfect.isPerfect_of_iso
    (ei ≪≫ (derivedExtensionScalars_id_iso.{u, max u v} K hK).some).symm hback

/-- Suppose a tower of rings has surjective transition maps with locally nilpotent kernels, and
its derived module objects are preserved by the base-change maps induced by their transitions.
If all terms are perfect, or one term is perfect and every subsequent transition kernel is
nilpotent, then every derived inverse limit over the vertex of the limit cone `c` is perfect and
its canonical base-change map to each term is an isomorphism. -/
@[stacks 0CQG]
public theorem derivedLimit_isPerfect_and_baseChange_iso
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A.obj (op n))))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj
        (Kₙ n))
    (hSurjective : ∀ n : ℕ,
      Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hLocallyNilpotent : ∀ n : ℕ,
      (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom).IsLocallyNilpotent)
    (hPerfect : (∀ n : ℕ, StacksDraft.Perfect.IsPerfect (Kₙ n)) ∨
      ∃ n₀ : ℕ, StacksDraft.Perfect.IsPerfect (Kₙ n₀) ∧
        ∀ n : ℕ, n₀ ≤ n →
          IsNilpotent (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom))
    (hBaseChange : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
        (A.map (homOfLE (Nat.le_succ n)).op).hom (φ n))) :
    let X : ℕ → DerivedCategory (ModuleCat.{max u v} c.pt) := fun n ↦
      (ModuleCat.restrictScalars (c.π.app (op n)).hom).mapDerivedCategory.obj (Kₙ n)
    let t : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
      (ModuleCat.restrictScalars (c.π.app (op (n + 1))).hom).mapDerivedCategory.map
          (φ n) ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp (c.π.app (op (n + 1))).hom
          (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
          (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (Kₙ n)
    ∀ [HasProduct X] (K : DerivedCategory (ModuleCat.{max u v} c.pt))
      (p : K ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ K⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk p
        (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{max u v} c.pt)) →
      StacksDraft.Perfect.IsPerfect K ∧ ∀ n : ℕ,
        IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
          (c.π.app (op n)).hom (p ≫ Pi.π X n)) := by
  have hdesc (n : ℕ) : StacksDraft.Perfect.IsPerfect (Kₙ n) →
      StacksDraft.Perfect.IsPerfect (Kₙ 0) := by
    induction n with
    | zero => exact id
    | succ n ih =>
      intro hn
      have := hBaseChange n
      exact ih <| StacksDraft.Perfect.isPerfect_of_iso
        (asIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
          (A.map (homOfLE (Nat.le_succ n)).op).hom (φ n))).symm
        (StacksDraft.Perfect.isPerfect_derivedExtensionScalars
          (A.map (homOfLE (Nat.le_succ n)).op).hom (Kₙ (n + 1)) hn)
  dsimp only
  intro _ K p δ htriangle
  obtain ⟨hK, hbase⟩ :=
    StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso
    A c hc Kₙ φ hSurjective hLocallyNilpotent
    (hPerfect.imp (fun h n => StacksDraft.Perfect.isPseudoCoherent_of_isPerfect _ (h n))
      fun ⟨n, hn, hnil⟩ => ⟨n, StacksDraft.Perfect.isPseudoCoherent_of_isPerfect _ hn, hnil⟩)
    hBaseChange K p δ htriangle
  refine ⟨isPerfect_of_surjective_baseChange (c.π.app (op 0)).hom
    (Concrete.surjective_π_app_zero_of_surjective_map hc hSurjective)
    (isUnit_of_isUnit_limit_projection_zero A c hc hSurjective hLocallyNilpotent) K hK
    (StacksDraft.Perfect.isPerfect_of_iso (@asIso _ _ _ _ _ (hbase 0)) ?_), hbase⟩
  exact hPerfect.elim (· 0) fun ⟨n, hn, _⟩ => hdesc n hn

/-! ### The adically complete case -/

section AdicallyComplete

open CategoryTheory.Pretriangulated

/-- Let `A` be `I`-adically complete and let `Kₙ n` be a derived object over
`A ⧸ I ^ (n + 1)`. Suppose `Kₙ 0` is perfect and every transition map becomes an isomorphism
after derived base change. Then a derived inverse limit `K` over `A` is perfect and derived
complete, and its canonical derived base-change map to every `Kₙ n` is an isomorphism. -/
@[stacks 09AW]
public theorem derivedLimit_isPerfect_isDerivedComplete_and_baseChange_iso
    (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))).mapDerivedCategory.obj (Kₙ n))
    (hPerfect : StacksDraft.Perfect.IsPerfect (Kₙ 0))
    (hBaseChange : ∀ n : ℕ, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
      (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) (φ n))) :
    letI : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} A) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v} A ℕ
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let q : ∀ n : ℕ, A ⧸ I ^ (n + 2) →+* A ⧸ I ^ (n + 1) := fun n ↦
      Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
    let a : ∀ n : ℕ, A →+* A ⧸ I ^ (n + 1) := fun n ↦
      Ideal.Quotient.mk (I ^ (n + 1))
    let X : ℕ → DerivedCategory (ModuleCat.{max u v} A) := fun n ↦
      (ModuleCat.restrictScalars (a n)).mapDerivedCategory.obj (Kₙ n)
    let t : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
      (ModuleCat.restrictScalars (a (n + 1))).mapDerivedCategory.map (φ n) ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp (a (n + 1)) (q n) (a n)
          (by ext x; rfl)).hom.app (Kₙ n)
    ∀ (K : DerivedCategory (ModuleCat.{max u v} A))
      (p : K ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{max u v} A)) →
        StacksDraft.Perfect.IsPerfect K ∧ _root_.IsDerivedComplete I K ∧
          ∀ n : ℕ, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
            (a n) (p ≫ Pi.π X n)) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} A) :=
    moduleCat_hasExactLimitsOfShape_discrete.{max u v} A ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  dsimp only
  intro K p δ hTriangle
  have hNilpotent (n : ℕ) :
      IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))) :=
    ⟨2, ker_factor_pow_eq_bot (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega))⟩
  have hLimit := derivedLimit_isPerfect_and_baseChange_iso
    (quotientPowerDiagram I) (quotientPowerCone I) (quotientPowerConeIsLimit I) Kₙ φ
    (fun n ↦ Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (fun n ↦ isLocallyNilpotent_of_isNilpotent _ (hNilpotent n))
    (Or.inr ⟨0, hPerfect, fun n _ ↦ hNilpotent n⟩) hBaseChange K p δ hTriangle
  have hComplete := derivedLimit_isPseudoCoherent_isDerivedComplete_and_baseChange_iso A I Kₙ φ
    (StacksDraft.Perfect.isPseudoCoherent_of_isPerfect _ hPerfect) hBaseChange K p δ hTriangle
  exact ⟨hLimit.1, hComplete.2.1, hLimit.2⟩

end AdicallyComplete

end StacksDraft.DerivedInverseLimit

end
