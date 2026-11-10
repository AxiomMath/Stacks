module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackSingleTorVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# Tor independence makes `g_*𝒪_{S'}` Tor-acyclic at the stalks, for `g` affine

Let `f : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes with `g` **affine**, and suppose `X`
and `S'` are Tor independent over `S` in the sense of [Stacks, Tag 08IA]
(`AlgebraicGeometry.TorIndependent`). Then the sheaf of `𝒪_S`-modules `g_*𝒪_{S'}` satisfies the
stalkwise Tor-vanishing predicate
`Stacks.Cohomology.PullbackSingleTor.StalkTorVanishing` of `f`: at every point `x` of `X` and
every `n > 0`,

`Tor_n^{𝒪_{S,f(x)}}(𝒪_{X,x}, (g_*𝒪_{S'})_{f(x)}) = 0`.

This is the Tor-vanishing input of step 4 of the proof of [Stacks, Tag 08IB], at the one sheaf
the tag applies it to.

## Main results

* `AlgebraicGeometry.stalkTorVanishing_pushforwardStructureSheaf`: the statement above.

## Implementation notes

*The affine chart.* Fix `x : X` and put `s = f(x)`. Choose an affine open `V ∋ s` of `S` and then
an affine open `U ∋ x` of `X` inside `f⁻¹V`, and write `R = Γ(S, V)`, `A = Γ(X, U)` and
`R' = Γ(S', g⁻¹V)`; the last open is affine because `g` is an affine morphism
(`AlgebraicGeometry.IsAffineOpen.preimage`). The affine criterion of [Stacks, Tag 0FXV],
`AlgebraicGeometry.torIndependent_tfae`, turns the hypothesis into Tor independence of
`R`, `A` and `R'`, and the three stalks in play are localizations of those three rings:
`𝒪_{S,s} = R_p` and `𝒪_{X,x} = A_q` by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`,
and `(g_*𝒪_{S'})_s` is the localization of `R'` at the image of the prime complement of `p`
— that is, `R' ⊗_R R_p` — by
`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`, where `p` and `q` are the
primes of `R` and `A` attached to `s` and `x` and `q` lies over `p`.

*The ring-theoretic step*, `torIndependent_of_isLocalization`, is one application of
[Stacks, Tag 08HW] (`RingTheory.TorIndependence.isIso_torExtensionMap_of_flat_sameUniverse`)
along the flat map `R → R_p`: the comparison `Tor_n^R(A, R') ⟶ Tor_n^{R_p}(A_q, R'_p)` is
invertible because all three of `R → R_p`, `A ⊗_R R_p → A_q` and `R_p ⊗_R R' → (g_*𝒪_{S'})_s`
are flat,
each being a localization — the second by `IsLocalization.isLocalization_of_submonoid_le`, since
`q` lies over `p` and so `q`'s prime complement contains the image of `p`'s.
No second, separate flat-extension step is needed.

*The two stalk spellings.* `Stacks.Cohomology.PullbackSingleTor.StalkTorVanishing` is stated at
the `RingCat`-valued stalk of the structure sheaf and at the `AddCommGrpCat`-valued stalk of the
module, whereas the localization statements above are about `CommRingCat`-valued stalks. The
first mismatch is bridged for Tor independence itself by `AlgebraicGeometry.torIndependent_congr`
along `SemilinearStalk.commStalkRingEquiv`, the germ maps being matched by
`Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso`. The second cannot be: the module stalk
carries no ring structure in that spelling, so `pushforwardStalkAddEquiv` below composes
`SemilinearStalk.commStalkRingEquiv` with `Stacks.AlgebraPullbackQcoh.unitAbStalkIso` — the
underlying presheaf of abelian groups of `g_*𝒪_{S'}` is `g.base _* 𝒪_{S'}` composed with the two
forgetful functors, both of which preserve the filtered colimit computing a stalk — and
`pushforwardStalkAddEquiv_smul` checks that the comparison is linear over the stalk of `𝒪_S`.
That is what feeds the vanishing into the predicate's second Tor argument.

## References

* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open AlgebraicGeometry.SheafOfModules
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The ring-theoretic step -/

/-- A ring map exhibiting a localization at a submonoid is flat. -/
private theorem flat_of_isLocalization {T L : Type u} [CommRing T] [CommRing L] (φ : T →+* L)
    (M : Submonoid T) (h : @IsLocalization T _ M L _ φ.toAlgebra) : φ.Flat := by
  let := φ.toAlgebra
  have := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat L M)
  rwa [RingHom.algebraMap_toAlgebra] at this

private theorem torIndependent_of_isLocalization
    {R A B Rp Aq Bp : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing Aq] [CommRing Bp]
    [Algebra R A] [Algebra R B]
    [Algebra R Rp] [Algebra A Aq] [Algebra B Bp]
    [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
    [IsScalarTower R A Aq] [IsScalarTower R Rp Aq]
    [IsScalarTower R B Bp] [IsScalarTower R Rp Bp]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hpq : q.comap (algebraMap R A) = p)
    [IsLocalization p.primeCompl Rp] [IsLocalization q.primeCompl Aq]
    [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) Bp]
    (h : RingTheory.TorIndependence.TorIndependent R A B) :
    RingTheory.TorIndependence.TorIndependent Rp Aq Bp := by
  have hRflat : RingHom.Flat (algebraMap R Rp) :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Rp p.primeCompl)
  let fA : A →ₐ[R] Aq := IsScalarTower.toAlgHom R A Aq
  let fB : B →ₐ[R] Bp := IsScalarTower.toAlgHom R B Bp
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩ hmem
    exact hr (hpq ▸ hmem)
  have hAflat : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R Rp Aq) (fun _ _ => Commute.all _ _)).toRingHom := by
    let ψ := Algebra.TensorProduct.lift fA (IsScalarTower.toAlgHom R Rp Aq)
      (fun _ _ => Commute.all _ _)
    let : Algebra (A ⊗[R] Rp) Aq := ψ.toRingHom.toAlgebra
    have : IsScalarTower A (A ⊗[R] Rp) Aq := IsScalarTower.of_algebraMap_eq' (by
      ext a
      change (algebraMap A Aq) a = ψ (algebraMap A (A ⊗[R] Rp) a)
      simp [ψ, Algebra.TensorProduct.algebraMap_apply, fA])
    have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] Rp) q.primeCompl) Aq :=
      IsLocalization.isLocalization_of_submonoid_le _ _
        (Algebra.algebraMapSubmonoid A p.primeCompl) _ hle
    exact flat_of_isLocalization _ (Algebra.algebraMapSubmonoid (A ⊗[R] Rp) q.primeCompl) this
  have hBflat : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R Rp Bp) fB (fun _ _ => Commute.all _ _)).toRingHom := by
    let : Algebra B (Rp ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    let ψ := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R Rp Bp) fB
      (fun _ _ => Commute.all _ _)
    let : Algebra (Rp ⊗[R] B) Bp := ψ.toRingHom.toAlgebra
    have : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) (Rp ⊗[R] B) :=
      IsLocalization.tensorRight (S := B) (A := Rp) p.primeCompl
    have : IsScalarTower B (Rp ⊗[R] B) Bp := IsScalarTower.of_algebraMap_eq' (by
      ext b
      change (algebraMap B Bp) b = ψ (algebraMap B (Rp ⊗[R] B) b)
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp [ψ, fB])
    have : IsLocalization (Algebra.algebraMapSubmonoid (Rp ⊗[R] B)
        (Algebra.algebraMapSubmonoid B p.primeCompl)) Bp :=
      IsLocalization.isLocalization_of_submonoid_le _ _
        (Algebra.algebraMapSubmonoid B p.primeCompl) _ le_rfl
    exact flat_of_isLocalization _ _ this
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  intro i hi
  let e := _root_.TorChangeOfRings.extensionMap
    _root_.TorChangeOfRings.canonicalSystem_nonempty
    R Rp A B Aq Bp i fA fB
  have he : IsIso e :=
    RingTheory.TorIndependence.isIso_torExtensionMap_of_flat_sameUniverse
      R Rp A B Aq Bp fA fB hRflat hAflat hBflat i
  have : Subsingleton (_root_.TorChangeOfRings.torObj R i A B) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((RingTheory.TorIndependence.torIndependent_iff_isZero_tor R A B).mp h i hi)
  have hbig := (asIso e).isZero_iff.mp ((ModuleCat.extendScalars _).map_isZero
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance))
  have : Subsingleton (_root_.TorChangeOfRings.torObj Rp i Aq Bp) :=
    (ModuleCat.isZero_iff_subsingleton.mp hbig :)
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-! ### The stalk of `g_*𝒪_{S'}` as a module over the stalk of `𝒪_S` -/

section Bridge

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (s : S)

/-- `g_*𝒪_{S'}`, read as a sheaf of `𝒪_S`-modules at the `structureSheafRing` spelling of the
structure sheaf of `S` — the spelling at which instance search finds the module structure on a
stalk. -/
private abbrev pushforwardUnitMod : SheafOfModules.{u} (structureSheafRing S.toRingedSpace) :=
  (Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf)

/-- The stalk at `s` of the comorphism `g^♯ : 𝒪_S ⟶ g_*𝒪_{S'}`, a map `𝒪_{S,s} ⟶ (g_*𝒪_{S'})_s`
of `CommRingCat`-valued stalks. The named accessor fixes the codomain to be the stalk of
`g.base _* 𝒪_{S'}`, which is the spelling the multiplication below has to be found at. -/
private abbrev pushforwardStalkRingMap :
    S.presheaf.stalk s ⟶
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) s :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} s).map g.c

/-- **The two stalks of `g_*𝒪_{S'}` at `s` agree.** The stalk of the sheaf of rings
`g_*𝒪_{S'}`, taken in `CommRingCat`, is the stalk of the underlying presheaf of abelian groups
of `g_*𝒪_{S'}` read as a sheaf of `𝒪_S`-modules, which is what
`AlgebraicGeometry.SheafOfModules.stalkFunctor` produces. Both forgetful functors
`CommRingCat ⥤ RingCat` and `RingCat ⥤ AddCommGrpCat` preserve the filtered colimit computing a
stalk, so this is `SemilinearStalk.commStalkRingEquiv` followed by
`Stacks.AlgebraPullbackQcoh.unitAbStalkIso`. -/
private def pushforwardStalkAddEquiv :
    (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) s : Type u) ≃+
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (pushforwardUnitMod g).val.presheaf s) :=
  (SemilinearStalk.commStalkRingEquiv (g.base _* S'.presheaf) s).symm.toAddEquiv.trans
    (Stacks.AlgebraPullbackQcoh.unitAbStalkIso
      ((g.base _* S'.presheaf) ⋙ forget₂ CommRingCat.{u} RingCat.{u})
        s).addCommGroupIsoToAddEquiv

/-- `pushforwardStalkAddEquiv` carries a germ to the germ of the same section. -/
private theorem pushforwardStalkAddEquiv_germ (V : S.Opens) (hs : s ∈ V) (b : Γ(S', g ⁻¹ᵁ V)) :
    pushforwardStalkAddEquiv g s (((g.base _* S'.presheaf).germ V s hs).hom b) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (pushforwardUnitMod g).val.presheaf V s hs).hom b := by
  have h1 : (SemilinearStalk.commStalkRingEquiv (g.base _* S'.presheaf) s).symm
      (((g.base _* S'.presheaf).germ V s hs).hom b) =
      (TopCat.Presheaf.germ (C := RingCat.{u})
        ((g.base _* S'.presheaf) ⋙ forget₂ CommRingCat.{u} RingCat.{u}) V s hs).hom b :=
    (RingEquiv.symm_apply_eq
        (SemilinearStalk.commStalkRingEquiv (g.base _* S'.presheaf) s)).mpr
      (SemilinearStalk.commStalkRingEquiv_germ (g.base _* S'.presheaf) s V hs b).symm
  exact (congrArg (AddCommGrpCat.Hom.hom (Stacks.AlgebraPullbackQcoh.unitAbStalkIso
      ((g.base _* S'.presheaf) ⋙ forget₂ CommRingCat.{u} RingCat.{u}) s).hom) h1).trans
    (Stacks.AlgebraPullbackQcoh.unitAbStalkIso_hom_germ
      ((g.base _* S'.presheaf) ⋙ forget₂ CommRingCat.{u} RingCat.{u}) s V hs b)

/-- **`pushforwardStalkAddEquiv` is linear over the stalk of `𝒪_S`.** Multiplication in
`(g_*𝒪_{S'})_s` by the image of an element of the `RingCat`-valued stalk `𝒪_{S,s}` under the
stalk of the comorphism `g^♯` corresponds to the module action of [Stacks, Tag 01CB] of that
element on the stalk of `g_*𝒪_{S'}` read as a module. Both sides are pinned by their effect on
germs: refining to a common neighbourhood `V ∋ s`, each is the germ of `g^♯(a) · b`. -/
private theorem pushforwardStalkAddEquiv_smul
    (lam : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing S.toRingedSpace).obj s))
    (t : (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) s : Type u)) :
    pushforwardStalkAddEquiv g s
        ((pushforwardStalkRingMap g s).hom
          (SemilinearStalk.commStalkRingEquiv S.presheaf s lam) * t)
      = lam • pushforwardStalkAddEquiv g s t := by
  obtain ⟨V₁, hV₁, a₀, ha⟩ :=
    TopCat.Presheaf.exists_germ_eq (structureSheafRing S.toRingedSpace).obj lam
  obtain ⟨V₂, hV₂, b₀, hb⟩ := TopCat.Presheaf.exists_germ_eq (g.base _* S'.presheaf) t
  have hmem : s ∈ V₁ ⊓ V₂ := ⟨hV₁, hV₂⟩
  set V := V₁ ⊓ V₂
  let a : (structureSheafRing S.toRingedSpace).obj.obj (op V) :=
    ((structureSheafRing S.toRingedSpace).obj.map (homOfLE inf_le_left).op).hom a₀
  let b : Γ(S', g ⁻¹ᵁ V) :=
    ((g.base _* S'.presheaf).map (homOfLE (inf_le_right : V ≤ V₂)).op).hom b₀
  have ha' : (TopCat.Presheaf.germ (C := RingCat.{u})
      (structureSheafRing S.toRingedSpace).obj V s hmem).hom a = lam := by
    rwa [show a = ((structureSheafRing S.toRingedSpace).obj.map (homOfLE inf_le_left).op).hom a₀
      from rfl, TopCat.Presheaf.germ_res_apply]
  have hb' : ((g.base _* S'.presheaf).germ V s hmem).hom b = t := by
    rwa [show b = ((g.base _* S'.presheaf).map (homOfLE (inf_le_right : V ≤ V₂)).op).hom b₀
      from rfl, TopCat.Presheaf.germ_res_apply]
  rw [← ha', ← hb']
  have e1 : SemilinearStalk.commStalkRingEquiv S.presheaf s
      ((TopCat.Presheaf.germ (C := RingCat.{u})
        (structureSheafRing S.toRingedSpace).obj V s hmem).hom a) =
      (S.presheaf.germ V s hmem).hom a :=
    SemilinearStalk.commStalkRingEquiv_germ S.presheaf s V hmem a
  rw [e1]
  have e2 : (pushforwardStalkRingMap g s).hom
      ((S.presheaf.germ V s hmem).hom a) =
      ((g.base _* S'.presheaf).germ V s hmem).hom ((g.app V).hom a) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V s hmem g.c a
  rw [e2, ← map_mul, pushforwardStalkAddEquiv_germ g s V hmem,
    pushforwardStalkAddEquiv_germ g s V hmem]
  exact germ_hom_smul (structureSheafRing S.toRingedSpace) s
    (pushforwardUnitMod g).val V hmem a b

end Bridge

/-! ### Tag 08IA makes `g_*𝒪_{S'}` Tor-acyclic at the stalks -/

/-- The germ of a pulled-back section is the image of the germ under the stalk map. -/
private theorem appLE_germ_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hxV : x ∈ V) (a : Γ(Y, U)) :
    (X.presheaf.germ V x hxV) (f.appLE U V e a) =
      (f.stalkMap x) ((Y.presheaf.germ U (f x) (e hxV)) a) := by
  rw [show f.appLE U V e a = (X.presheaf.map (homOfLE e).op) ((f.app U) a) from rfl,
    X.presheaf.germ_res_apply (homOfLE e) x hxV]
  exact (Scheme.Hom.germ_stalkMap_apply f U x (e hxV) a).symm

/-- **Tor independence makes `g_*𝒪_{S'}` Tor-acyclic at the stalks.** For a morphism of schemes
`f : X ⟶ S` and an affine morphism `g : S' ⟶ S` with `X` and `S'` Tor independent over `S`
([Stacks, Tag 08IA]), the sheaf `g_*𝒪_{S'}` of `𝒪_S`-modules satisfies the stalkwise
Tor-vanishing predicate of `f`: at every `x : X` and every `n > 0`,

`Tor_n^{𝒪_{S,f(x)}}(𝒪_{X,x}, (g_*𝒪_{S'})_{f(x)}) = 0`.

This is the Tor-vanishing input of step 4 of the proof of [Stacks, Tag 08IB]. Neither
quasi-coherence, nor quasi-compactness, nor a Cartesian square is assumed. -/
theorem stalkTorVanishing_pushforwardStructureSheaf
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom g]
    (hTor : AlgebraicGeometry.TorIndependent f g) :
    Stacks.Cohomology.PullbackSingleTor.StalkTorVanishing f.toLRSHom.toShHom
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf)) := by
  intro x n hn
  -- An affine open `V ∋ f(x)` of `S` and an affine open `U ∋ x` of `X` inside `f⁻¹V`.
  obtain ⟨-, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hsV (V.2.preimage f.continuous)
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  -- The three rings of sections and the two structure maps between them.
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S', g ⁻¹ᵁ V) := (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  have hCrit := ((AlgebraicGeometry.torIndependent_tfae f g).out 1 2).mp hTor
  have hring : RingTheory.TorIndependence.TorIndependent Γ(S, V) Γ(X, U) Γ(S', g ⁻¹ᵁ V) :=
    (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).2
      (hCrit U hU (g ⁻¹ᵁ V) hV' V hV hUV le_rfl)
  -- The two primes, and the fact that one lies over the other.
  set p := (hV.primeIdealOf ⟨f.base x, hsV⟩).asIdeal
  set q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : p.IsPrime := (hV.primeIdealOf ⟨f.base x, hsV⟩).isPrime
  have : q.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  have hpq : q.comap (algebraMap Γ(S, V) Γ(X, U)) = p :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU).1)
  -- The three stalks are localizations of the three rings of sections.
  let : Algebra Γ(S, V) (S.presheaf.stalk (f.base x)) :=
    S.presheaf.algebra_section_stalk ⟨f.base x, hsV⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : Algebra Γ(S', g ⁻¹ᵁ V)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) :=
    ((g.base _* S'.presheaf).germ V (f.base x) hsV).hom.toAlgebra
  have : IsLocalization p.primeCompl (S.presheaf.stalk (f.base x)) :=
    hV.isLocalization_stalk ⟨f.base x, hsV⟩
  have : IsLocalization q.primeCompl (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have happ : (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom = (g.app V).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app g)
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(S', g ⁻¹ᵁ V) p.primeCompl)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) := by
    change IsLocalization (p.primeCompl.map (algebraMap Γ(S, V) Γ(S', g ⁻¹ᵁ V))) _
    rw [show (algebraMap Γ(S, V) Γ(S', g ⁻¹ᵁ V)) = (g.app V).hom from
      (RingHom.algebraMap_toAlgebra _).trans happ]
    exact hV.isLocalization_pushforwardStalk g hsV
  -- The three structure maps between the stalks, and the four towers over `Γ(S, V)`.
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base x))
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) :=
    (pushforwardStalkRingMap g (f.base x)).hom.toAlgebra
  let : Algebra Γ(S, V) (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (f.appLE V U hUV).hom).toAlgebra
  let : Algebra Γ(S, V)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) :=
    (((g.base _* S'.presheaf).germ V (f.base x) hsV).hom.comp
      (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom).toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, V) Γ(S', g ⁻¹ᵁ V)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, V) (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq (appLE_germ_eq f hUV x hxU)
  have : IsScalarTower Γ(S, V) (S.presheaf.stalk (f.base x))
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change ((g.base _* S'.presheaf).germ V (f.base x) hsV).hom
          ((g.appLE V (g ⁻¹ᵁ V) le_rfl).hom a) = _
      rw [happ]
      exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V (f.base x) hsV g.c a).symm
  -- The ring-theoretic step: Tor independence of the three stalks.
  have hstalk : RingTheory.TorIndependence.TorIndependent (S.presheaf.stalk (f.base x))
      (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) :=
    torIndependent_of_isLocalization p q hpq hring
  -- Transport to the `RingCat`-valued stalk of the structure sheaf.
  let := Stacks.RingedSpace.structureStalkCommRing S.toRingedSpace (f.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X.toRingedSpace x
  let : Algebra (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing S.toRingedSpace).obj (f.base x)))
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing X.toRingedSpace).obj x)) :=
    (Stacks.RingedSpace.stalkRingMap f.toLRSHom.toShHom x).hom.toAlgebra
  let : Algebra (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing S.toRingedSpace).obj (f.base x)))
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x) :
        Type u) :=
    ((pushforwardStalkRingMap g (f.base x)).hom.comp
      (SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).toRingHom).toAlgebra
  have hA : ∀ r, (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm
      (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) r) =
      algebraMap _ _ ((SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).symm r) := by
    intro r
    refine ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm_apply_eq).mpr ?_
    have key := DFunLike.congr_fun (congrArg RingCat.Hom.hom
      (Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso f.toLRSHom.toShHom x))
      ((SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).symm r)
    change (SemilinearStalk.commStalkRingEquiv X.presheaf x)
        ((Stacks.RingedSpace.stalkRingMap f.toLRSHom.toShHom x).hom _) =
      (f.stalkMap x).hom ((SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x))
        ((SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).symm r)) at key
    rw [RingEquiv.apply_symm_apply] at key
    exact key.symm
  have hB : ∀ r, (RingEquiv.refl _)
      (algebraMap (S.presheaf.stalk (f.base x))
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x)) r) =
      algebraMap _ _ ((SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).symm r) :=
    fun r => congrArg (pushforwardStalkRingMap g (f.base x)).hom
      ((SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).apply_symm_apply r).symm
  have hbig := (AlgebraicGeometry.torIndependent_congr _ _ _ _ _ _
      (SemilinearStalk.commStalkRingEquiv S.presheaf (f.base x)).symm
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm (RingEquiv.refl _) hA hB).mp hstalk
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor] at hbig
  -- The `ModuleCat` identification the predicate asks for.
  let iB : ModuleCat.of (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing S.toRingedSpace).obj (f.base x)))
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (g.base _* S'.presheaf) (f.base x) :
        Type u) ≅
      (stalkFunctor (structureSheafRing S.toRingedSpace) (f.base x)).obj
        (pushforwardUnitMod g) :=
    LinearEquiv.toModuleIso
      { toFun := pushforwardStalkAddEquiv g (f.base x)
        invFun := (pushforwardStalkAddEquiv g (f.base x)).symm
        left_inv := (pushforwardStalkAddEquiv g (f.base x)).left_inv
        right_inv := (pushforwardStalkAddEquiv g (f.base x)).right_inv
        map_add' := (pushforwardStalkAddEquiv g (f.base x)).map_add
        map_smul' := pushforwardStalkAddEquiv_smul g (f.base x) }
  exact ((((Tor (ModuleCat.{u} (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing S.toRingedSpace).obj (f.base x)))) n).obj
        (CochainComplex.DerivedExtensionScalars.baseModule
          (Stacks.RingedSpace.stalkRingMap f.toLRSHom.toShHom x).hom)).mapIso iB).isZero_iff).mp
    (hbig n hn)

end AlgebraicGeometry

end
