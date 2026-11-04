module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingChartHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.RingTheory.AdicCompletion.FiniteBaseChange
public import StacksFrontier.RingTheory.HenselizationUniverse.StrictTensorProduct

/-!
# Tor independence of schemes and of the algebraic spaces they represent

Tor independence of two schemes over a base, Stacks 08IA, is a condition on their *ordinary*
local rings, whereas Tor independence of two algebraic spaces over a base, Stacks 08IP, is a
condition on their *étale* local rings.  Condition (4) of Stacks 08IQ is condition (3) of that
tag — one étale surjective diagram of charts suffices — for a diagram whose three upper terms
are schemes, with Tor independence read in the sense of Stacks 08IA.  This file relates the two
notions on such a diagram and so proves that condition (4) implies condition (1).

The comparison is the proof of Stacks 08IQ for condition (4).  The étale local ring of an
algebraic space at a geometric point is a strict henselization of the ordinary local ring of a
scheme chart at the point under the chosen lift (Stacks 04KF), the structure map being the
canonical map of Stacks 05VP, and for a representable algebraic space the chart may be taken to
be the identity.  The square of the four local rings attached to a morphism of schemes commutes
by Stacks 05VU.  Stacks 08HV then identifies `𝒪_{U, ū}` with a strict henselization of a
localization of `𝒪_{W, w̄} ⊗_{𝒪_{W, w}} 𝒪_{U, u}`, so the base change map is flat; Stacks 0FXF
and Stacks 08HW carry Tor independence along the flat base change `𝒪_{W, w} → 𝒪_{W, w̄}` and
the two flat changes of the algebras.

## Main results

* `RingTheory.TorIndependence.torIndependent_of_flat_lifts`: Tor independence passes along a
  flat base change of the base ring together with flat changes of the two algebras.
* `IsLocalRing.IsHenselization.flat_tensorProduct_lift`: Stacks 08HV read as flatness of the
  map `A ⊗_R R' → A'` between two strict henselizations over a local homomorphism.
* `AlgebraicGeometry.Space.isHenselization_etaleLocalRing_chart`: Stacks 04KF with the structure
  map named as the canonical map of Stacks 05VP.
* `AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing_yoneda`: the
  square of Stacks 05VU at the identity charts of two representable algebraic spaces.
* `AlgebraicGeometry.Space.torIndependent_yoneda_of_torIndependent_scheme`: Tor independence of
  two schemes over a base scheme, Stacks 08IA, gives Tor independence of the algebraic spaces
  they represent, Stacks 08IP.
* `AlgebraicGeometry.Space.torIndependent_of_torIndependent_scheme_diagram`: Stacks 08IQ,
  condition (4) implies condition (1).

## Implementation notes

`RingTheory.TorIndependence.torIndependent_of_flat_lifts` crosses the two universes in its first
step only: ordinary local rings of schemes lie in `Type u` and étale local rings of algebraic
spaces in `Type (u + 1)`, and Stacks 0FXF is the one statement of the theory that is proved at
independent universes.  Its second step, Stacks 08HW, is then applied with all six rings in
`Type (u + 1)`, which is what lets the single-universe reformulations of Tor independence be
used.  Stacks 08HV is taken in the source-strength form
`StacksDraft.strictHenselization_tensorProduct_at_induced_prime`, whose six rings carry six
independent universes; the single-universe provider would not apply.

The three charts are the identity charts `AlgebraicGeometry.Space.yonedaIdentityNeighborhood` of
the three representable spaces.  Their virtue is that the target neighbourhood of the square of
Stacks 05VU is again an identity chart, on the nose, so the point of the chart of the base is
the image of the point of the chart of the source with no transport; the only transport in the
comparison is along the equality of the two geometric points of the base, and
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_yonedaIdentityNeighborhood_congr`
carries it, the identity chart being a function of the geometric point.

The converse implication, condition (1) implies condition (4), is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeConverse`.  It asks for Tor
independence of the *ordinary* local rings, which by Stacks 08HX has to be checked after
localizing at every prime of the tensor product, and the geometric points realizing such a prime
are produced from it there.

Three ingredients of that converse are supplied here and in the files this one imports.
`RingHom.Flat.tensorProduct_of_flat_lifts` makes the map `A₀ ⊗_{R₀} C₀ → A' ⊗_{R'} C'` flat
under exactly the hypotheses of Stacks 08HW, so
`RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_flat_lifts` descends the
vanishing of `Tor^{R'}(A', C')` to the vanishing of `Tor^{R₀}(A₀, C₀)` localized at every prime
of `A₀ ⊗_{R₀} C₀` which is the contraction of a prime of `A' ⊗_{R'} C'`, which is the form in
which condition (3) of Stacks 08HX asks for it.  The prime upstairs is produced as the kernel of
an evaluation at a geometric point, and
`AlgebraicGeometry.Space.geometricEval_comp_of_relativelyRepresentable` is what makes the two
evaluations of such a pair agree over the base: the triangle of geometric evaluations commutes on
the *whole* étale local ring for a representable morphism, base change of pointed charts
supplying a commuting square of charts over every chart of the target.

## References

* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 08HV](https://stacks.math.columbia.edu/tag/08HV)
* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [Stacks Project, Tag 0FXF](https://stacks.math.columbia.edu/tag/0FXF)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v

open scoped TensorProduct

namespace RingTheory.TorIndependence

/-- **Tor independence passes along a flat base change together with flat changes of the two
algebras.**  Let `R → R'` be flat, let `A` and `B` be `R`-algebras and let `A'` and `B'` be
`R'`-algebras receiving `A` and `B` over `R` by maps whose lifts `A ⊗_R R' → A'` and
`B ⊗_R R' → B'` are flat.  Then Tor independence of `A` and `B` over `R` gives Tor independence
of `A'` and `B'` over `R'`.

This is Stacks 0FXF followed by Stacks 08HW: the first step replaces `A` and `B` by their base
changes `A ⊗_R R'` and `B ⊗_R R'`, which is where the two universes are crossed, and the second
compares the Tor modules of those with the Tor modules of `A'` and `B'` over the one ring `R'`.
The universes are those of the application: the two sides of the comparison of conditions (1)
and (4) of Stacks 08IQ are ordinary local rings of schemes and étale local rings of algebraic
spaces, which live one universe apart. -/
theorem torIndependent_of_flat_lifts
    {R A B : Type u} {R' A' B' : Type (u + 1)}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R'] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hR' : RingHom.Flat (algebraMap R R'))
    (hA : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R R' A') fun _ _ => Commute.all _ _).toRingHom)
    (hB : RingHom.Flat (Algebra.TensorProduct.lift fB
      (IsScalarTower.toAlgHom R R' B') fun _ _ => Commute.all _ _).toRingHom)
    (h : TorIndependent R A B) :
    TorIndependent R' A' B' := by
  let : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  let : Algebra R' (B ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  have h1 : TorIndependent R' (A ⊗[R] R') (B ⊗[R] R') :=
    torIndependent_tensorProduct_of_flat R R' A B h hR'
  let gA : (A ⊗[R] R') →ₐ[R'] A' :=
    { (Algebra.TensorProduct.lift fA (IsScalarTower.toAlgHom R R' A')
        fun _ _ => Commute.all _ _) with
      commutes' := fun r => by
        show Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ[R] r) = _
        rw [Algebra.TensorProduct.lift_tmul]
        simp }
  let gB : (B ⊗[R] R') →ₐ[R'] B' :=
    { (Algebra.TensorProduct.lift fB (IsScalarTower.toAlgHom R R' B')
        fun _ _ => Commute.all _ _) with
      commutes' := fun r => by
        show Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ[R] r) = _
        rw [Algebra.TensorProduct.lift_tmul]
        simp }
  rw [torIndependent_iff_subsingleton_tor] at h1 ⊢
  intro i hi
  let : Subsingleton (TorChangeOfRings.torObj R' i (A ⊗[R] R') (B ⊗[R] R')) := h1 i hi
  let e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
    R' R' (A ⊗[R] R') (B ⊗[R] R') A' B' i gA gB
  have he : IsIso e := TorChangeOfRings.isIso_extensionMap_of_flat_algebra
    TorChangeOfRings.canonicalSystem_nonempty R' (A ⊗[R] R') (B ⊗[R] R') A' B' gA gB hA hB i
  have hz := (asIso e).isZero_iff.mp ((ModuleCat.extendScalars _).map_isZero
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance))
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  exact hs

end RingTheory.TorIndependence

namespace IsLocalRing.IsHenselization

/-- **A strict henselization is flat over the base change of the base's strict
henselization, at a pair of primes.**  Let `R → S` be a ring map, let `q ⊆ S` be a prime lying
over `p ⊆ R`, let `Rsh` be a strict henselization of `R_p` and `Ssh` one of `S_q`, and let the
square of the four rings commute.  Then the induced map `S ⊗_R Rsh → Ssh` is flat.

This is Stacks 08HV: that map identifies `Ssh` with a strict henselization of a localization of
`Rsh ⊗_R S`, and both a localization and a strict henselization are flat.  The map of Stacks
08HV is the unique local `R`-algebra homomorphism `Rsh → Ssh` inducing the given homomorphism of
residue fields, which is what pins it to be the one carried by the commuting square. -/
theorem flat_tensorProduct_lift_atPrime
    {R S : Type u} {Rp Sq : Type u} {Rsh Ssh : Type v} {LR LS : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [CommRing Sq] [IsLocalRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra R Sq] [Algebra Rp Sq] [IsScalarTower R S Sq] [IsScalarTower R Rp Sq]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rp Rsh] [IsScalarTower R Rp Rsh]
    [CommRing Ssh] [IsLocalRing Ssh] [Algebra R Ssh] [Algebra S Ssh] [Algebra Rp Ssh]
    [Algebra Sq Ssh] [IsScalarTower R S Ssh] [IsScalarTower S Sq Ssh] [IsScalarTower R Rp Ssh]
    [IsScalarTower Rp Sq Ssh]
    [Algebra Rsh Ssh] [IsScalarTower R Rsh Ssh] [IsLocalHom (algebraMap Rsh Ssh)]
    [Field LR] [Algebra (ResidueField Rp) LR] [IsSepClosure (ResidueField Rp) LR]
    [IsHenselization Rp LR Rsh]
    [Field LS] [Algebra (ResidueField Sq) LS] [IsSepClosure (ResidueField Sq) LS]
    [IsHenselization Sq LS Ssh] :
    RingHom.Flat (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S Ssh)
      (IsScalarTower.toAlgHom R Rsh Ssh) fun _ _ => Commute.all _ _).toRingHom := by
  obtain ⟨algR, hhR, hsepR, -⟩ :=
    exists_residueFieldAlgebra (R := Rp) (L := LR) (Rh := Rsh)
  obtain ⟨algS, hhS, hsepS, -⟩ :=
    exists_residueFieldAlgebra (R := Sq) (L := LS) (Rh := Ssh)
  let := algR
  let := algS
  let := hhR
  let := hhS
  let := hsepR inferInstance
  let := hsepS inferInstance
  set phi : ResidueField Rsh →+* ResidueField Ssh :=
    ResidueField.map (algebraMap Rsh Ssh)
  have hphires : (residue Ssh).comp (algebraMap Rsh Ssh) = phi.comp (residue Rsh) :=
    RingHom.ext fun x => (ResidueField.map_residue (algebraMap Rsh Ssh) x).symm
  have hphi : phi.comp ((residue Rsh).comp (algebraMap R Rsh)) =
      (residue Ssh).comp (algebraMap R Ssh) := by
    rw [← RingHom.comp_assoc, ← hphires, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R Rsh Ssh]
  obtain ⟨f, hfloc, hfres, huniq, Q, hQ, -, -, -, alg, hlocHom, algRes, -, hhens, -, hcomp⟩ :=
    StacksDraft.strictHenselization_tensorProduct_at_induced_prime
      (R := R) (Rp := Rp) (Rsh := Rsh) (S := S) (Sq := Sq) (Ssh := Ssh) p q phi hphi
  let := alg
  let := algRes
  let := hhens
  have hlocTower : IsLocalHom (IsScalarTower.toAlgHom R Rsh Ssh) :=
    ⟨fun a ha => IsLocalHom.map_nonunit (f := algebraMap Rsh Ssh) a ha⟩
  have hf : IsScalarTower.toAlgHom R Rsh Ssh = f :=
    huniq _ hlocTower hphires.symm
  have hflatQ : RingHom.Flat (algebraMap (Localization.AtPrime Q) Ssh) := by
    have : Module.Flat (Localization.AtPrime Q) Ssh :=
      IsHenselization.flat (R := Localization.AtPrime Q) (L := ResidueField Ssh) (Rh := Ssh)
    exact RingHom.flat_algebraMap_iff.mpr this
  have hflatLoc : RingHom.Flat (algebraMap (Rsh ⊗[R] S) (Localization.AtPrime Q)) :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.AtPrime Q) Q.primeCompl)
  have hflatg : RingHom.Flat (Algebra.TensorProduct.lift f
      (IsScalarTower.toAlgHom R S Ssh) fun _ _ => Commute.all _ _).toRingHom := by
    rw [← hcomp]
    exact hflatLoc.comp hflatQ
  set c : (S ⊗[R] Rsh) →+* (Rsh ⊗[R] S) :=
    (Algebra.TensorProduct.comm R S Rsh).toAlgHom.toRingHom
  have hcbij : Function.Bijective c := (Algebra.TensorProduct.comm R S Rsh).bijective
  have hswap : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S Ssh)
        (IsScalarTower.toAlgHom R Rsh Ssh) fun _ _ => Commute.all _ _).toRingHom =
      (Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Ssh)
          fun _ _ => Commute.all _ _).toRingHom.comp c := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      have hca : c (a ⊗ₜ[R] r) = r ⊗ₜ[R] a := rfl
      simp only [RingHom.comp_apply, hca, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, ← hf]
      exact Commute.all _ _
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  rw [hswap]
  exact (RingHom.Flat.of_bijective hcbij).comp hflatg

/-- **A strict henselization is flat over the base change of the base's strict
henselization.**  Let `R → A` be a local homomorphism of local rings, let `R → R'` and `A → A'`
be strict henselizations, and suppose the square of the four rings commutes.  Then the induced
map `A ⊗_R R' → A'` is flat.

This is Stacks 08HV: that map identifies `A'` with a strict henselization of a localization of
`R' ⊗_R A`, and both a localization and a strict henselization are flat.  The map of Stacks
08HV is the unique local `R`-algebra homomorphism `R' → A'` inducing the given homomorphism of
residue fields, which is what pins it to be the one carried by the commuting square. -/
theorem flat_tensorProduct_lift
    {R A : Type u} {R' A' : Type v} {LR LA : Type*}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing R'] [IsLocalRing A']
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Algebra R R'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [Algebra R' A'] [IsScalarTower R R' A'] [IsLocalHom (algebraMap R' A')]
    [Field LR] [Algebra (ResidueField R) LR] [IsSepClosure (ResidueField R) LR]
    [IsHenselization R LR R']
    [Field LA] [Algebra (ResidueField A) LA] [IsSepClosure (ResidueField A) LA]
    [IsHenselization A LA A'] :
    RingHom.Flat (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
      (IsScalarTower.toAlgHom R R' A') fun _ _ => Commute.all _ _).toRingHom := by
  let : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalRing.isLocalization_atPrime_maximalIdeal R
  let : IsLocalization.AtPrime A (maximalIdeal A) :=
    IsLocalRing.isLocalization_atPrime_maximalIdeal A
  let : (maximalIdeal A).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R A)).symm⟩
  exact flat_tensorProduct_lift_atPrime (R := R) (S := A) (Rp := R) (Sq := A)
    (Rsh := R') (Ssh := A') (LR := LR) (LS := LA) (maximalIdeal R) (maximalIdeal A)

end IsLocalRing.IsHenselization

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04KF, with the structure map pinned.**  The étale local ring of an algebraic space
at a geometric point is a strict henselization of the local ring of a scheme chart at the point
under the chosen lift, the structure map being the canonical map of Stacks 05VP.

This is `AlgebraicGeometry.Space.exists_algebra_isHenselization_etaleLocalRing_chart` with the
algebra structure named rather than produced, which is what the comparison of conditions (1) and
(4) of Stacks 08IQ needs: the square of Stacks 05VU, which relates the structure maps of two
charts over a morphism, is a statement about the map of Stacks 05VP. -/
theorem isHenselization_etaleLocalRing_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS X x) := isLocalRing_etaleLocalRing B S hS X hX x
    letI : Algebra ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x) :=
      (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
    IsHenselization ↥(chartLocalRing B S hS X V)
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField) ↥(etaleLocalRing B S hS X x) := by
  let : IsLocalRing ↥(etaleLocalRing B S hS X x) := isLocalRing_etaleLocalRing B S hS X hX x
  let : Algebra ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  exact IsHenselization.of_ringEquiv (chartStrictHenselizationEquiv B S hS X hX V) fun _ => rfl

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP at the identity chart of a
representable algebraic space is compatible with an equality of geometric points. -/
theorem chartLocalRingToEtaleLocalRing_yonedaIdentityNeighborhood_congr (U₀ : BigFppfOver B S hS)
    {z₁ z₂ : GeometricPoint B S hS (yoneda.obj U₀)} (hz : z₁ = z₂)
    (h₁ : chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ z₁) =
      chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ z₂))
    (h₂ : etaleLocalRing B S hS (yoneda.obj U₀) z₁ = etaleLocalRing B S hS (yoneda.obj U₀) z₂) :
    (eqToHom h₂).hom.comp (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U₀)
        (isAlgebraicSpace_yoneda B S hS U₀) (yonedaIdentityNeighborhood U₀ z₁)) =
      (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U₀)
        (isAlgebraicSpace_yoneda B S hS U₀) (yonedaIdentityNeighborhood U₀ z₂)).comp
        (eqToHom h₁).hom := by
  cases hz
  simp

/-- **The commuting square of local rings of Stacks 05VU at the identity charts of two
representable algebraic spaces.**  For a morphism `g : U ⟶ W` of the big fppf site and a
geometric point `ū` of `U`, the two composites `𝒪_{W, w} → 𝒪_{W, w̄} → 𝒪_{U, ū}` and
`𝒪_{W, w} → 𝒪_{U, u} → 𝒪_{U, ū}` agree, the étale charts being the identities. -/
theorem etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing_yoneda
    {U₀ W₀ : BigFppfOver B S hS} (gU : U₀ ⟶ W₀)
    (ubar : GeometricPoint B S hS (yoneda.obj U₀)) :
    (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
          (yonedaIdentityNeighborhood U₀ ubar)).comp
        (((BigFppfOver.toScheme B S hS).map gU).stalkMap
          (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))).hom =
      (etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map gU) ubar).comp
        (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj W₀)
          (isAlgebraicSpace_yoneda B S hS W₀)
          (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar))) :=
  etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS
    (Xs := ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩)
    (Ys := ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩)
    (ObjectProperty.homMk (yoneda.map gU)) ubar (yonedaIdentityNeighborhood U₀ ubar)
    (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)).chart gU (by simp)

/-- A local homomorphism precomposed with a transport along an equality of objects of
`CommRingCat` is a local homomorphism. -/
private theorem isLocalHom_eqToHom_comp {R₁ R₂ C : CommRingCat.{v}} (hR : R₁ = R₂)
    [IsLocalRing R₁] [IsLocalRing R₂] [IsLocalRing C]
    (ψ : R₂ ⟶ C) (hψ : IsLocalHom ψ.hom) :
    IsLocalHom ((eqToHom hR ≫ ψ).hom) := by
  cases hR
  simpa using hψ

/-- **Stacks 08IQ, the comparison of conditions (4) and (1) on one diagram of schemes.**  Let
`U ⟶ W ⟵ V` be morphisms of the big fppf site of `S`.  If the schemes underlying `U` and `V`
are Tor independent over the scheme underlying `W` in the sense of Stacks 08IA, that is on their
ordinary local rings, then the algebraic spaces they represent are Tor independent over the
algebraic space `W` represents in the sense of Stacks 08IP, that is on their étale local rings.

The étale local ring at a geometric point is a strict henselization of the ordinary local ring
of the chart under the point, Stacks 04KF, and the canonical map of Stacks 05VP is its structure
map; Stacks 05VU says the square of the four local rings over `U ⟶ W` commutes.  Stacks 08HV
then identifies `𝒪_{U, ū}` with a strict henselization of a localization of
`𝒪_{W, w̄} ⊗_{𝒪_{W, w}} 𝒪_{U, u}`, so the base change map is flat, and Tor independence passes
along it. -/
theorem torIndependent_yoneda_of_torIndependent_scheme
    {U₀ V₀ W₀ : BigFppfOver B S hS} (gU : U₀ ⟶ W₀) (gV : V₀ ⟶ W₀)
    (h : AlgebraicGeometry.TorIndependent ((BigFppfOver.toScheme B S hS).map gU)
      ((BigFppfOver.toScheme B S hS).map gV)) :
    TorIndependent (isAlgebraicSpace_yoneda B S hS U₀) (isAlgebraicSpace_yoneda B S hS V₀)
      (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map gU) (yoneda.map gV) := by
  intro ubar vbar hpt
  refine ⟨etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map gU) ubar,
    etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map gV) vbar,
    etaleLocalRingMap_isEtaleLocalRingMap _ _ _,
    etaleLocalRingMap_isEtaleLocalRingMap _ _ _, ?_⟩
  -- the equality of the two points of the chart of the base under the two geometric points
  have h₀ : chartPoint B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)) =
      chartPoint B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gV) vbar)) :=
    congrArg (fun z : GeometricPoint B S hS (yoneda.obj W₀) =>
      (show ↥((BigFppfOver.toScheme B S hS).obj W₀) from
        chartPoint B S hS (yoneda.obj W₀) (yonedaIdentityNeighborhood W₀ z))) hpt
  have h₁ : chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)) =
      chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gV) vbar)) :=
    congrArg (fun z : GeometricPoint B S hS (yoneda.obj W₀) =>
      (show CommRingCat.{u} from chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ z))) hpt
  have h₂ : etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map gU) ubar) =
      etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map gV) vbar) :=
    congrArg (etaleLocalRing B S hS (yoneda.obj W₀)) hpt
  -- the local-ring structures on the four étale local rings
  let : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS U₀) ubar
  let : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS V₀) vbar
  let : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj W₀)
      (geometricPointMap (yoneda.map gU) ubar)) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS W₀) _
  let : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj W₀)
      (geometricPointMap (yoneda.map gV) vbar)) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS W₀) _
  -- the two stalk maps of the morphisms of schemes, as in Stacks 08IA
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar)) :=
    (((BigFppfOver.toScheme B S hS).map gU).stalkMap
      (chartPoint B S hS (yoneda.obj U₀)
        (yonedaIdentityNeighborhood U₀ ubar))).hom.toAlgebra
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar)) :=
    ((eqToHom h₁ ≫ ((BigFppfOver.toScheme B S hS).map gV).stalkMap
      (chartPoint B S hS (yoneda.obj V₀)
        (yonedaIdentityNeighborhood V₀ vbar))).hom).toAlgebra
  -- the three structure maps of Stacks 05VP
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map gU) ubar)) :=
    (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B S hS W₀)
      (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar))).toAlgebra
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj U₀)
        (yonedaIdentityNeighborhood U₀ ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀) (yonedaIdentityNeighborhood U₀ ubar)).toAlgebra
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj V₀)
        (yonedaIdentityNeighborhood V₀ vbar))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀) (yonedaIdentityNeighborhood V₀ vbar)).toAlgebra
  -- the two canonical maps of étale local rings of Stacks 04NG
  let : Algebra ↥(etaleLocalRing B S hS (yoneda.obj W₀)
        (geometricPointMap (yoneda.map gU) ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    (etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map gU) ubar).toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS (yoneda.obj W₀)
        (geometricPointMap (yoneda.map gU) ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    ((eqToHom h₂ ≫ CommRingCat.ofHom (etaleLocalRingMap
      (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map gV) vbar)).hom).toAlgebra
  -- the two composites out of the local ring of the chart of the base
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    ((chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀)
      (yonedaIdentityNeighborhood U₀ ubar)).comp
      (((BigFppfOver.toScheme B S hS).map gU).stalkMap
        (chartPoint B S hS (yoneda.obj U₀)
          (yonedaIdentityNeighborhood U₀ ubar))).hom).toAlgebra
  let : Algebra ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    ((chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀)
      (yonedaIdentityNeighborhood V₀ vbar)).comp
      ((eqToHom h₁ ≫ ((BigFppfOver.toScheme B S hS).map gV).stalkMap
        (chartPoint B S hS (yoneda.obj V₀)
          (yonedaIdentityNeighborhood V₀ vbar))).hom)).toAlgebra
  let : IsScalarTower ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the two scalar towers through the étale local ring of the base, which are Stacks 05VU
  let : IsScalarTower ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map gU) ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun
      (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing_yoneda B S hS gU ubar) x
  let : IsScalarTower ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map gU) ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      have hcg := DFunLike.congr_fun
        (chartLocalRingToEtaleLocalRing_yonedaIdentityNeighborhood_congr B S hS W₀ hpt h₁ h₂) x
      have hsqV := DFunLike.congr_fun
        (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing_yoneda B S hS gV vbar)
        ((eqToHom h₁).hom x)
      simp only [RingHom.comp_apply] at hcg hsqV
      show chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V₀)
          (isAlgebraicSpace_yoneda B S hS V₀) (yonedaIdentityNeighborhood V₀ vbar)
          ((((BigFppfOver.toScheme B S hS).map gV).stalkMap
            (chartPoint B S hS (yoneda.obj V₀)
              (yonedaIdentityNeighborhood V₀ vbar))).hom ((eqToHom h₁).hom x)) =
        etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map gV) vbar
          ((eqToHom h₂).hom (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj W₀)
            (isAlgebraicSpace_yoneda B S hS W₀)
            (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)) x))
      rw [hcg]
      exact hsqV
  -- the four maps out of the base are local homomorphisms
  let : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS (yoneda.obj W₀)
      (geometricPointMap (yoneda.map gU) ubar)) ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar)) :=
    isLocalHom_etaleLocalRingMap B S hS (isAlgebraicSpace_yoneda B S hS U₀)
      (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map gU) ubar
  let : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS (yoneda.obj W₀)
      (geometricPointMap (yoneda.map gU) ubar)) ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar)) :=
    isLocalHom_eqToHom_comp h₂ _ (isLocalHom_etaleLocalRingMap B S hS
      (isAlgebraicSpace_yoneda B S hS V₀) (isAlgebraicSpace_yoneda B S hS W₀)
      (yoneda.map gV) vbar)
  let : IsLocalHom (algebraMap ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar))) :=
    isLocalHom_eqToHom_comp h₁
      (((BigFppfOver.toScheme B S hS).map gV).stalkMap
        (chartPoint B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar)))
      (((BigFppfOver.toScheme B S hS).map gV).prop _)
  let : IsLocalHom (algebraMap ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))) :=
    ((BigFppfOver.toScheme B S hS).map gU).prop _
  -- the étale local rings are strict henselizations of the chart local rings, Stacks 04KF
  let := isHenselization_etaleLocalRing_chart B S hS (isAlgebraicSpace_yoneda B S hS W₀)
    (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar))
  let := isHenselization_etaleLocalRing_chart B S hS (isAlgebraicSpace_yoneda B S hS U₀)
    (yonedaIdentityNeighborhood U₀ ubar)
  let := isHenselization_etaleLocalRing_chart B S hS (isAlgebraicSpace_yoneda B S hS V₀)
    (yonedaIdentityNeighborhood V₀ vbar)
  let LW := separableClosure (ResidueField ↥(chartLocalRing B S hS (yoneda.obj W₀)
      (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar))))
    (chartGeometricPoint (yonedaIdentityNeighborhood W₀
      (geometricPointMap (yoneda.map gU) ubar))).residueField
  exact RingTheory.TorIndependence.torIndependent_of_flat_lifts
    (IsScalarTower.toAlgHom
      ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar))
    (IsScalarTower.toAlgHom
      ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar))
    (flat_chartLocalRingToEtaleLocalRing B S hS (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B S hS W₀)
      (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
    (IsLocalRing.IsHenselization.flat_tensorProduct_lift
      (LR := LW)
      (LA := separableClosure (ResidueField ↥(chartLocalRing B S hS (yoneda.obj U₀)
          (yonedaIdentityNeighborhood U₀ ubar)))
        (chartGeometricPoint (yonedaIdentityNeighborhood U₀ ubar)).residueField))
    (IsLocalRing.IsHenselization.flat_tensorProduct_lift
      (LR := LW)
      (LA := separableClosure (ResidueField ↥(chartLocalRing B S hS (yoneda.obj V₀)
          (yonedaIdentityNeighborhood V₀ vbar)))
        (chartGeometricPoint (yonedaIdentityNeighborhood V₀ vbar)).residueField))
    ((RingTheory.TorIndependence.torIndependent_iff_isZero_tor
      ↥(chartLocalRing B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ (geometricPointMap (yoneda.map gU) ubar)))
      ↥(chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))
      ↥(chartLocalRing B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar))).mpr
      (h (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))
        (chartPoint B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar)) h₀))


/-! ### Stacks 08IQ, condition (4) implies condition (1) -/

/-- **Stacks 08IQ, (4) ⟹ (1).**  Let `X` and `Y` be algebraic spaces over an algebraic space
`Bs`.  Suppose given one commutative diagram
```
U ⟶ W ⟵ V
↓    ↓    ↓
X ⟶ Bs ⟵ Y
```
in which `U`, `V` and `W` are *schemes*, the vertical arrows are étale, `W ⟶ Bs` is surjective
and `U` and `V` are étale and surjective over the fibre products `X ×_{Bs} W` and `Y ×_{Bs} W`.
If `U` and `V` are Tor independent over `W` in the sense of Stacks 08IA, that is on their
ordinary local rings, then `X` and `Y` are Tor independent over `Bs`.

This is condition (4) of Stacks 08IQ: a diagram as in condition (3) whose three upper terms are
schemes, with Tor independence read in the sense of Derived Categories of Schemes, Definition
08IA.  The passage from the ordinary local rings of the three schemes to the étale local rings
of the algebraic spaces they represent is
`AlgebraicGeometry.Space.torIndependent_yoneda_of_torIndependent_scheme`; condition (3) then
gives condition (1) by
`AlgebraicGeometry.Space.torIndependent_of_isEtale_surjective_diagram`. -/
@[stacks 08IQ "(4) => (1)"]
theorem torIndependent_of_torIndependent_scheme_diagram
    {Bs X Y PX PY : AlgebraicSpaces B S hS} (fX : X ⟶ Bs) (gY : Y ⟶ Bs)
    {U₀ V₀ W₀ : BigFppfOver B S hS}
    (c : yoneda.obj W₀ ⟶ Bs.1) (a : yoneda.obj U₀ ⟶ X.1) (uw : U₀ ⟶ W₀)
    (b : yoneda.obj V₀ ⟶ Y.1) (vw : V₀ ⟶ W₀)
    (pX : PX ⟶ X) (pW : PX.1 ⟶ yoneda.obj W₀) (qY : PY ⟶ Y) (qW : PY.1 ⟶ yoneda.obj W₀)
    (u' : yoneda.obj U₀ ⟶ PX.1) (v' : yoneda.obj V₀ ⟶ PY.1)
    (sqX : IsPullback pX.hom pW fX.hom c) (sqY : IsPullback qY.hom qW gY.hom c)
    (hu'X : u' ≫ pX.hom = a) (hu'W : u' ≫ pW = yoneda.map uw)
    (hv'Y : v' ≫ qY.hom = b) (hv'W : v' ≫ qW = yoneda.map vw)
    (hcEtale : IsEtale B S hS c) (hcSurj : IsSurjective B S hS c)
    (haEtale : IsEtale B S hS a) (hbEtale : IsEtale B S hS b)
    (huEtale : IsEtale B S hS u') (huSurj : IsSurjective B S hS u')
    (hvEtale : IsEtale B S hS v') (hvSurj : IsSurjective B S hS v')
    (h : AlgebraicGeometry.TorIndependent ((BigFppfOver.toScheme B S hS).map uw)
      ((BigFppfOver.toScheme B S hS).map vw)) :
    TorIndependent X.2 Y.2 Bs.2 fX.hom gY.hom :=
  torIndependent_of_isEtale_surjective_diagram B S hS
    (U := ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩)
    (V := ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩)
    (W := ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩) fX gY
    (ObjectProperty.homMk c) (ObjectProperty.homMk a) (ObjectProperty.homMk (yoneda.map uw))
    (ObjectProperty.homMk b) (ObjectProperty.homMk (yoneda.map vw)) pX
    (ObjectProperty.homMk pW) qY (ObjectProperty.homMk qW) (ObjectProperty.homMk u')
    (ObjectProperty.homMk v') sqX sqY (by apply ObjectProperty.hom_ext; exact hu'X)
    (by apply ObjectProperty.hom_ext; exact hu'W) (by apply ObjectProperty.hom_ext; exact hv'Y)
    (by apply ObjectProperty.hom_ext; exact hv'W)
    hcEtale hcSurj haEtale hbEtale huEtale huSurj hvEtale hvSurj
    (torIndependent_yoneda_of_torIndependent_scheme B S hS uw vw h)

end AlgebraicGeometry.Space

end

