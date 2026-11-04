module

public import StacksFrontier.AlgebraicGeometry.Descent.CubeTrivialNearFibre
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SpanRestrictInvertible
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.Homology.Perfect.FlatComplexFibreVanishing

/-!
# The triviality locus of the theorem of the cube is closed

Let `h : P ⟶ Spec A` be proper, flat, of finite presentation and geometrically integral, and let
`L` be an invertible module on `P`. If `L` is trivial on the fibres over primes `q` arbitrarily
close to a prime `p` (every `D(a) ∋ p` contains such a `q`), then `L` is trivial on the fibre over
`p`. This is the closedness step of the proof of [Stacks, Tag 0BF4] (the source gets it from
[Stacks, Tag 0BF0]); the argument is the classical one: `h⁰(L_q) > 0` and `h⁰(L_q^{-1}) > 0` are
closed conditions by semicontinuity, and on an integral fibre with `Γ(𝒪) = κ` both of them
together force `L_p` to be trivial.

## Main results

* `Stacks.Cube.exists_away_subsingleton_sections`: if a flat finitely presented module has no
  nonzero global sections on the fibre over `p`, the same holds on every base change over some
  `D(a) ∋ p`.
* `Stacks.Cube.tensorPairing_ne_zero_of_isIntegral`: on an integral scheme, the product of nonzero
  global sections of `L` and of an inverse of `L` is nonzero.
* `Stacks.Cube.nonempty_iso_unit_fibre_of_forall_away`: the closedness step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry.DescentLocusComparison
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpGerm grpStalk ringGerm)

universe u

namespace Stacks.Cube

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Vanishing of global sections on a fibre spreads out.** Let `f : X ⟶ Spec A` be proper and
locally of finite presentation, and `M` a finitely presented module on `X` flat over `A`. If `M`
has no nonzero global section on the fibre over a prime `p`, there is `a ∉ p` such that `M` has no
nonzero global section on any base change of `X` along a ring map inverting `a`. This is the
semicontinuity of `h⁰` ([Stacks, Tag 0BDN]) in the form needed here, obtained from the Čech complex
of `M`, which is a perfect complex of flat modules computing `RΓ` after every base change. -/
theorem exists_away_subsingleton_sections {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] (hM : IsFlatOver f.toLRSHom.toShHom M)
    (p : Ideal A) [p.IsPrime] {X₀ : Scheme.{u}} {g₀ : X₀ ⟶ X}
    {f₀ : X₀ ⟶ Spec (.of p.ResidueField)}
    (hsq₀ : IsPullback g₀ f₀ f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (h₀ : Subsingleton Γ((Scheme.Modules.pullback g₀).obj M, ⊤)) :
    ∃ a : A, a ∉ p ∧ ∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ a) →
      ∀ {Y : Scheme.{u}} {g : Y ⟶ X} {h : Y ⟶ Spec (.of B)},
        IsPullback g h f (Spec.map (CommRingCat.ofHom φ)) →
        Subsingleton Γ((Scheme.Modules.pullback g).obj M, ⊤) := by
  classical
  have : M.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation M
  obtain ⟨I, _, _, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  set D := baseAlternatingCechComplex f U hU M
  have hDperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj D) :=
    StacksDraft.Perfect.isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU M haff)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper f M hM)
  have : ∀ i, Module.Flat A (D.X i) := flat_baseAlternatingCechComplex_X f U hU M hUaff hM
  obtain ⟨a, ha, hB⟩ := StacksDraft.Perfect.exists_away_isZero_homology_extendScalars_of_fibre
    D 0 (Fintype.card I) hDperf p 0 (fun i hi => by
      rcases lt_or_eq_of_le hi with hi | rfl
      · exact ShortComplex.isZero_homology_of_isZero_X₂ _
          ((StacksDraft.Perfect.extendScalarsCx _ D).isZero_of_isStrictlyGE 0 i hi)
      · have e := homologyZeroModelEquiv (algebraMap A p.ResidueField) hsq₀ M U hU hUaff (𝟙 D) hM
          (Fintype.card I)
        have : Subsingleton ((StacksDraft.Perfect.extendScalarsCx
            (algebraMap A p.ResidueField) D).homology 0) := e.toEquiv.subsingleton
        exact ModuleCat.isZero_of_subsingleton _)
  refine ⟨a, ha, fun B _ φ hφ Y g h hsq => ?_⟩
  have e := homologyZeroModelEquiv φ hsq M U hU hUaff (𝟙 D) hM (Fintype.card I)
  have : Subsingleton ((StacksDraft.Perfect.extendScalarsCx φ D).homology 0) :=
    ModuleCat.subsingleton_of_isZero (hB φ hφ 0 le_rfl)
  exact e.symm.toEquiv.subsingleton

/-- A module with more than one element has a nonzero element. -/
theorem exists_ne_zero_of_not_subsingleton {M : Type*} [AddCommGroup M] (h : ¬ Subsingleton M) :
    ∃ m : M, m ≠ 0 := by
  by_contra hne
  exact h ⟨fun a b => (not_not.1 fun ha => hne ⟨a, ha⟩).trans
    (not_not.1 fun hb => hne ⟨b, hb⟩).symm⟩

section Pairing

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- **On an integral scheme, two nonzero global sections pair to a nonzero function.** Let `ψ`
trivialize `L ⊗ N` on an integral locally noetherian scheme `Y`, with `L` and `N` invertible.
Nonzero global sections `m` of `L` and `n` of `N` have nonzero germs at the generic point, whose
stalks are lines over the function field; their product is therefore nonzero there. -/
theorem tensorPairing_ne_zero_of_isIntegral {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {L N : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y N]
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
    {m : Γ(L, ⊤)} {n : Γ(N, ⊤)} (hm : m ≠ 0) (hn : n ≠ 0) :
    Stacks.SheafOfModules.tensorPairing (X := Y.toRingedSpace) ψ ⊤ m n ≠ 0 := by
  intro h0
  set η := genericPoint Y
  let : Field (ringStalk Y.toRingedSpace η) := inferInstanceAs (Field Y.functionField)
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Y.toRingedSpace L.val η
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Y.toRingedSpace N.val η
  have hgm : grpGerm Y.toRingedSpace L.val η ⊤ trivial m ≠ 0 :=
    Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero L hm
  have hgn : grpGerm Y.toRingedSpace N.val η ⊤ trivial n ≠ 0 :=
    Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero N hn
  have hpair := Stacks.SheafOfModules.stalkPairing_germ ψ η ⊤ trivial m n
  have h1 : Stacks.SheafOfModules.stalkPairing ψ η
      (grpGerm Y.toRingedSpace L.val η ⊤ trivial m ⊗ₜ[ringStalk Y.toRingedSpace η]
        grpGerm Y.toRingedSpace N.val η ⊤ trivial n) = 0 := by
    rw [hpair, h0]
    try exact map_zero _
  exact Stacks.SheafOfModules.tmul_ne_zero_of_ne_zero (K := ringStalk Y.toRingedSpace η) hgm hgn
    ((LinearEquiv.map_eq_zero_iff _).1 h1)

/-- **An invertible module with nonzero sections of itself and of its inverse on an integral
fibre is trivial.** Let `g : Y ⟶ X` with `Y` integral, locally noetherian, with `Γ(Y, 𝒪) = K`. If
the pullbacks of `L` and of `L^{⊗ -1}` both have nonzero global sections, their product is a
nonzero constant, hence a unit, and a section pairing to a unit trivializes `g^* L`. -/
theorem nonempty_iso_unit_of_ne_zero_of_ne_zero {K : Type u} [Field K] {X Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] {π : Y ⟶ Spec (.of K)}
    (hΓ : Function.Bijective (Stacks.Cech.globalRingHom π).hom) (g : Y ⟶ X) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {m : Γ((Scheme.Modules.pullback g).obj L, ⊤)}
    {n : Γ((Scheme.Modules.pullback g).obj
      (Stacks.SheafOfModules.Invertible.tensorPowerModule L (-1)), ⊤)}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    Nonempty ((Scheme.Modules.pullback g).obj L ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) := by
  have hLag : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.SheafOfModules.Invertible.tensorPowerModule L (-1)) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower X.presheaf X.ringCatSheaf.2 L (-1)
  have : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback g).obj L) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  have : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback g).obj
      (Stacks.SheafOfModules.Invertible.tensorPowerModule L (-1))) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  set ψ := Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso g L
  set c : Γ(Y, ⊤) := Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOne g L m n
  have hc : c ≠ 0 := tensorPairing_ne_zero_of_isIntegral ψ hm hn
  obtain ⟨k, hk⟩ := hΓ.2 c
  have hk0 : k ≠ 0 := by rintro rfl; exact hc (by rw [← hk, map_zero])
  obtain ⟨u, hu⟩ : IsUnit c := hk ▸ (isUnit_iff_ne_zero.mpr hk0).map _
  have hsmul : Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOne g L m
      (((u⁻¹ : Γ(Y, ⊤)ˣ) : Γ(Y, ⊤)) • n) = ((u⁻¹ : Γ(Y, ⊤)ˣ) : Γ(Y, ⊤)) * c := by
    rw [← Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneLinear_tmul,
      TensorProduct.tmul_smul, map_smul, smul_eq_mul]
    rfl
  refine Stacks.SheafOfModules.nonempty_iso_unit_of_tensorPairing_eq_unitSection
    (X := Y.toRingedSpace) ψ m (((u⁻¹ : Γ(Y, ⊤)ˣ) : Γ(Y, ⊤)) • n) ?_
  refine hsmul.trans ?_
  rw [← hu]
  exact u.inv_mul

end Pairing

section Closed

variable {A : Type u} [CommRing A] {P : Scheme.{u}} (h : P ⟶ Spec (.of A))

/-- The fibre of a proper geometrically integral morphism over a prime is integral, locally
noetherian, and has `Γ(𝒪) = κ`. -/
theorem fibre_isIntegral_and [IsProper h] [Flat h] [LocallyOfFinitePresentation h]
    [GeometricallyIntegral h] (q : Ideal A) [q.IsPrime] :
    IsIntegral (pullback h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField)))) ∧
      IsLocallyNoetherian
        (pullback h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField)))) ∧
      Function.Bijective (Stacks.Cech.globalRingHom
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).hom :=
  ⟨GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd h _),
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h _),
    bijective_globalRingHom_of_geometricallyIntegral _⟩

/-- **The closedness step of the theorem of the cube, over an affine base.** Let
`h : P ⟶ Spec A` be proper, flat, locally of finite presentation and geometrically integral, and
`L` an invertible module on `P`. If every basic open `D(a) ∋ p` contains a prime `q` over which
`L` is trivial on the fibre, then `L` is trivial on the fibre over `p`.

By `exists_away_subsingleton_sections`, applied to `L` and to `L^{⊗ -1}`, both have nonzero
global sections on the fibre over `p` (on the fibres over the nearby `q` they do: `L` because it
is trivial there, `L^{⊗ -1}` because a section of it pairs with one of `L` to `1`); on the
integral fibre over `p` this makes `L` trivial (`nonempty_iso_unit_of_ne_zero_of_ne_zero`). -/
theorem nonempty_iso_unit_fibre_of_forall_away [IsProper h] [Flat h]
    [LocallyOfFinitePresentation h] [GeometricallyIntegral h] (L : P.Modules)
    [Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L] (p : Ideal A) [p.IsPrime]
    (hcl : ∀ a : A, a ∉ p → ∃ (q : Ideal A) (_ : q.IsPrime), a ∉ q ∧
      Nonempty ((Scheme.Modules.pullback
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).obj L ≅
          _root_.SheafOfModules.unit
            (pullback h
              (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField)))).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).obj L ≅
        _root_.SheafOfModules.unit
          (pullback h
            (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).ringCatSheaf) := by
  classical
  have hLag : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  set N := Stacks.SheafOfModules.Invertible.tensorPowerModule L (-1)
  have : Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 N :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower P.presheaf P.ringCatSheaf.2 L (-1)
  have : L.IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_of_isInvertible_ringedSpace P.toRingedSpace L
      inferInstance
  have : N.IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_of_isInvertible_ringedSpace P.toRingedSpace N
      inferInstance
  have hLf : IsFlatOver h.toLRSHom.toShHom L := isFlatOver_of_isInvertible h L
  have hNf : IsFlatOver h.toLRSHom.toShHom N := isFlatOver_of_isInvertible h N
  -- on the fibres over the nearby primes both modules have nonzero sections
  have hnear : ∀ (q : Ideal A) [q.IsPrime],
      Nonempty ((Scheme.Modules.pullback
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).obj L ≅
          _root_.SheafOfModules.unit
            (pullback h
              (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField)))).ringCatSheaf) →
      ¬ Subsingleton Γ((Scheme.Modules.pullback
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).obj L, ⊤) ∧
      ¬ Subsingleton Γ((Scheme.Modules.pullback
        (pullback.fst h
          (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).obj N, ⊤) := by
    intro q _ ⟨e⟩
    obtain ⟨-, -, hΓ⟩ := fibre_isIntegral_and h q
    have hΓ' := bijective_baseRingHom_of_eq_top _ rfl hΓ
    have hnt : Nontrivial Γ(pullback h
        (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))), ⊤) := by
      refine ⟨⟨1, 0, fun h10 => one_ne_zero (hΓ.1 ?_)⟩⟩
      rw [map_one, map_zero]
      exact h10
    refine ⟨fun hsub => ?_, fun hsub => ?_⟩
    · have e' := sectionsEquivOfIsoUnit _ e hΓ'
      have := e'.symm.toEquiv.subsingleton
      exact not_subsingleton q.ResidueField inferInstance
    · obtain ⟨m, n, hmn⟩ :=
        Stacks.AlgebraicGeometry.PicardBaseChange.exists_pullbackMulNegOne_eq_one _ L ⟨e⟩
      rw [Subsingleton.elim n 0,
        ← Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneLinear_tmul,
        TensorProduct.tmul_zero, map_zero] at hmn
      exact zero_ne_one hmn
  -- semicontinuity at `p`
  have hfar : ∀ (M : P.Modules) [M.IsFinitePresentation], IsFlatOver h.toLRSHom.toShHom M →
      (∀ (q : Ideal A) [q.IsPrime],
        Nonempty ((Scheme.Modules.pullback
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).obj L ≅
            _root_.SheafOfModules.unit (pullback h
              (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField)))).ringCatSheaf) →
        ¬ Subsingleton Γ((Scheme.Modules.pullback
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A q.ResidueField))))).obj M,
            ⊤)) →
      ¬ Subsingleton Γ((Scheme.Modules.pullback
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).obj M,
          ⊤) := by
    intro M _ hMf hM hsub
    obtain ⟨a, ha, hB⟩ := exists_away_subsingleton_sections h M hMf p
      (IsPullback.of_hasPullback _ _) hsub
    obtain ⟨q, _, haq, he⟩ := hcl a ha
    refine hM q he (hB q.ResidueField (algebraMap A q.ResidueField) ?_
      (IsPullback.of_hasPullback _ _))
    refine isUnit_iff_ne_zero.mpr fun h0 => haq ?_
    exact Ideal.algebraMap_residueField_eq_zero.mp h0
  have hL0 := hfar L hLf fun q _ he => (hnear q he).1
  have hN0 := hfar N hNf fun q _ he => (hnear q he).2
  obtain ⟨m, hm⟩ := exists_ne_zero_of_not_subsingleton hL0
  obtain ⟨n, hn⟩ := exists_ne_zero_of_not_subsingleton hN0
  obtain ⟨_, _, hΓ⟩ := fibre_isIntegral_and h p
  exact nonempty_iso_unit_of_ne_zero_of_ne_zero hΓ _ L hm hn

end Closed

end Stacks.Cube

end
