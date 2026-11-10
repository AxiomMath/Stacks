module

public import Mathlib.RingTheory.Localization.Free
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.RingTheory.Ideal.CotangentLocalization
public import StacksFrontier.RingTheory.Module.Kaplansky
public import StacksFrontier.RingTheory.Smooth.Conormal
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# A smooth section has a formal power series neighbourhood

Near a point of a section where the morphism is smooth, the section has affine neighbourhoods with
free conormal module and power-series formal completion.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.sectionAlgHom` is the algebra homomorphism on sections induced by
  a section of a morphism of schemes, over compatible affine opens.

## Main results

* `AlgebraicGeometry.exists_affineOpens_free_conormal_powerSeries` gives compatible affine
  neighbourhoods, a free conormal module, and a formal power series description of the completion
  along the section.

## Implementation notes

The two neighbourhoods are chosen simultaneously: the same section ideal is used for both the
conormal module and the completion. The induced algebra map on sections is identified with the
section's restriction, rather than chosen arbitrarily. `Ideal.Cotangent` represents `I/I²`.

The construction of that algebra map from a section is needed twice, once for the neighbourhoods
produced by smoothness and once for the smaller pair on which the conormal module becomes free.
It is therefore isolated as `AlgebraicGeometry.Scheme.Hom.sectionAlgHom`, resting on
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE_eq_id`, so that the main proof instantiates one
construction twice instead of repeating it.

## References

* [Stacks Project, Tag 05D9](https://stacks.math.columbia.edu/tag/05D9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The identity morphism acts as the identity on the sections over any open. -/
public lemma appLE_id_eq {S : Scheme.{u}} (U : S.Opens) :
    Scheme.Hom.appLE (𝟙 S) U U (by simp) = 𝟙 Γ(S, U) := by
  have e : U ≤ (𝟙 S) ⁻¹ᵁ U := by simp
  change Scheme.Hom.app (𝟙 S) U ≫ S.presheaf.map (homOfLE e).op = _
  rw [Scheme.Hom.id_app]
  change 𝟙 Γ(S, U) ≫ S.presheaf.map (𝟙 U).op = _
  simp

/-- For a section `σ` of `f` and compatible opens, the maps on sections induced by `f` and by `σ`
compose to the identity. -/
public lemma appLE_comp_appLE_eq_id {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (U : S.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hUV : U ≤ σ ⁻¹ᵁ V) :
    f.appLE U V hVU ≫ σ.appLE V U hUV = 𝟙 Γ(S, U) := by
  simpa only [hσ, appLE_id_eq] using Scheme.Hom.appLE_comp_appLE σ f U V U hVU hUV

/-- The algebra homomorphism on sections induced by a section `σ` of `f`, for the algebra
structure that `f` puts on the sections over compatible affine opens. -/
public def sectionAlgHom {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (U : S.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hUV : U ≤ σ ⁻¹ᵁ V) :
    letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    Γ(X, V) →ₐ[Γ(S, U)] Γ(S, U) :=
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  { toRingHom := (σ.appLE V U hUV).hom
    commutes' := fun x => by
      change (σ.appLE V U hUV).hom ((f.appLE U V hVU).hom x) = x
      simpa [RingHom.comp_apply] using congrArg (fun q : Γ(S, U) →+* Γ(S, U) => q x)
        (congrArg CommRingCat.Hom.hom (appLE_comp_appLE_eq_id f σ hσ U V hVU hUV)) }

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- A map of rings under a common base is a map of algebras for the induced algebra structures. -/
private alias isScalarTower_of_hom_comp_eq :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.isScalarTower_of_comp_eq

/-- Restricting the map on sections induced by a section `σ` to smaller compatible opens gives the
same map whether the target or the source is restricted first. -/
private theorem appLE_restrict_comm {X S : Scheme.{u}} (σ : S ⟶ X) {U U' : S.Opens}
    {V V' : X.Opens} (hUV : U ≤ σ ⁻¹ᵁ V) (hU'V' : U' ≤ σ ⁻¹ᵁ V') (hU'U : U' ≤ U)
    (hV'V : V' ≤ V) :
    σ.appLE V U hUV ≫ S.presheaf.map (homOfLE hU'U).op =
      X.presheaf.map (homOfLE hV'V).op ≫ σ.appLE V' U' hU'V' := by
  calc
    _ = σ.appLE V U' (hU'U.trans hUV) :=
      Scheme.Hom.appLE_map σ hUV (homOfLE hU'U).op
    _ = _ := by
      symm
      convert Scheme.Hom.map_appLE σ hU'V' (homOfLE hV'V).op using 1

/-- `AlgebraicGeometry.appLE_restrict_comm` read as an identity of ring homomorphisms. -/
private theorem appLE_restrict_comm_hom {X S : Scheme.{u}} (σ : S ⟶ X) {U U' : S.Opens}
    {V V' : X.Opens} (hUV : U ≤ σ ⁻¹ᵁ V) (hU'V' : U' ≤ σ ⁻¹ᵁ V') (hU'U : U' ≤ U)
    (hV'V : V' ≤ V) :
    (σ.appLE V' U' hU'V').hom.comp (X.presheaf.map (homOfLE hV'V).op).hom =
      (S.presheaf.map (homOfLE hU'U).op).hom.comp (σ.appLE V U hUV).hom :=
  (congrArg CommRingCat.Hom.hom (appLE_restrict_comm σ hUV hU'V' hU'U hV'V)).symm

/-- Scalars pass through an intermediate algebra: if `A → A' → L` is a tower of algebras and `N`
carries compatible `A`-, `A'`- and `L`-actions, then `A → A' → N` is a tower. -/
private theorem isScalarTower_of_tower_smul (L : Type*) {A A' N : Type*} [CommRing A]
    [CommRing A'] [CommRing L] [AddCommMonoid N] [Algebra A A'] [Algebra A' L] [Algebra A L]
    [IsScalarTower A A' L] [Module A N] [Module A' N] [Module L N] [IsScalarTower A' L N]
    [IsScalarTower A L N] : IsScalarTower A A' N :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    calc
      (algebraMap A A' r) • x = algebraMap A' L (algebraMap A A' r) • x :=
        (IsScalarTower.algebraMap_smul (R := A') (A := L) (M := N) (algebraMap A A' r) x).symm
      _ = algebraMap A L r • x :=
        congrArg (fun z : L => z • x) (IsScalarTower.algebraMap_apply A A' L r).symm
      _ = r • x := IsScalarTower.algebraMap_smul (R := A) (A := L) (M := N) r x

/-- Freeness transfers along a ring isomorphism: a module free over `R` is free over `R'` once the
`R'`-action is the `R`-action read through an isomorphism `R ≃+* R'`. -/
private theorem free_of_ringEquiv {R R' N : Type*} [CommRing R] [CommRing R'] [AddCommGroup N]
    [Module R N] [Module R' N] (e : R ≃+* R') (hsmul : ∀ (r : R) (x : N), r • x = e r • x)
    (hfree : Module.Free R N) : Module.Free R' N := by
  have := hfree
  let : RingHomInvPair (e : R →+* R') (e.symm : R' →+* R) := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair (e.symm : R' →+* R) (e : R →+* R') := RingHomInvPair.of_ringEquiv_symm e
  let eId : N ≃ₛₗ[(e : R →+* R')] N :=
    { toFun := id, invFun := id
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := hsmul }
  exact Module.Free.of_equiv (σ' := (e.symm : R' →+* R)) eId

/-- **The kernel of a localized section.** If a ring map `ψ : B → A` sends the powers of `b` onto
the powers of `h`, and `ψ' : B' → A'` agrees with `ψ` on `B` for the away-localizations at `b` and
`h`, then `ψ'` is the localization of `ψ`, so its kernel is generated by that of `ψ`. -/
private theorem ker_eq_map_of_localized {A B A' B' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] (ψ : B →+* A) (ψ' : B' →+* A')
    (b : B) (h : A) [IsLocalization.Away b B'] [IsLocalization.Away h A']
    (hsub : Submonoid.map ψ (.powers b) = .powers h)
    (hcomm : ψ'.comp (algebraMap B B') = (algebraMap A A').comp ψ) :
    RingHom.ker ψ' = (RingHom.ker ψ).map (algebraMap B B') := by
  have hden : .powers b ≤ Submonoid.comap ψ (.powers h) := by
    rw [← hsub]
    exact Submonoid.le_comap_map (S := .powers b) (f := ψ)
  have hsection : ψ' = IsLocalization.map A' ψ hden := by
    apply IsLocalization.ringHom_ext (.powers b)
    rw [hcomm]
    exact (IsLocalization.map_comp hden).symm
  rw [hsection]
  exact IsLocalization.ker_map (S := B') A' ψ hsub

/-- A point of an affine open lies in the basic open of a section that is outside the prime ideal
of that point. -/
private theorem mem_basicOpen_of_notMem_primeIdealOf {S : Scheme.{u}} {U : S.Opens}
    (hU : IsAffineOpen U) (x : U) (h : Γ(S, U)) (hh : h ∉ (hU.primeIdealOf x).asIdeal) :
    (x : S) ∈ S.basicOpen h := by
  have hq : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ S.basicOpen h := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact hh
  have hs : hU.fromSpec (hU.primeIdealOf x) ∈ S.basicOpen h := hq
  simpa [hU.fromSpec_primeIdealOf] using hs

/-- A basic open of the base contained in `σ ⁻¹ᵁ W` lies in the preimage under the section `σ` of
the basic open of `W` cut out by the pullback of the same function. -/
private theorem basicOpen_le_preimage_basicOpen_appLE {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {T : S.Opens} {W : X.Opens} (hWT : W ≤ f ⁻¹ᵁ T) (g : Γ(S, T))
    (hg : S.basicOpen g ≤ σ ⁻¹ᵁ W) :
    S.basicOpen g ≤ σ ⁻¹ᵁ X.basicOpen ((f.appLE T W hWT).hom g) := by
  intro y hy
  rw [Scheme.basicOpen_appLE f _ _ hWT g]
  refine ⟨hg hy, ?_⟩
  have hfy : f (σ y) = y := by simpa using congrArg (fun q : S ⟶ S => q y) hσ
  change f (σ y) ∈ S.basicOpen g
  rw [hfy]
  exact hy

/-- An algebra map `B →ₐ[A] A` carries the powers of the image of `h` onto the powers of `h`. -/
private theorem map_powers_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (ψ : B →ₐ[A] A) (h : A) :
    Submonoid.map ψ.toRingHom (.powers (algebraMap A B h)) = .powers h := by
  rw [Submonoid.map_powers]
  congr 1
  exact ψ.commutes h

/-- **Compatible affine neighbourhoods at a smooth point of a section.** Where `f` is smooth along
the section `σ`, the point `s` has an affine neighbourhood `U` and `σ s` an affine neighbourhood
`V` mapping into it, such that `Γ(X, V)` is a smooth `Γ(S, U)`-algebra. Both are basic opens of a
pair given by smoothness, which is what makes the sections over them a localization. -/
private theorem exists_affineOpens_smooth {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (s : S) (hsmooth : InfinitesimalLifting.SmoothAt f (σ s)) :
    ∃ (U : S.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : s ∈ U)
      (_ : σ s ∈ V) (hVU : V ≤ f ⁻¹ᵁ U) (_ : U ≤ σ ⁻¹ᵁ V),
      letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
      Algebra.Smooth Γ(S, U) Γ(X, V) := by
  obtain ⟨W, T, hW, hT, hxW, hWT, hsmoothRing⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine f (σ s)).mp hsmooth
  have hsW : s ∈ σ ⁻¹ᵁ W := hxW
  have hσs : f (σ s) = s := by simpa using congrArg (fun q : S ⟶ S => q s) hσ
  have hsT : s ∈ T := by simpa [hσs] using (hWT hxW)
  have hsTW : s ∈ T ⊓ σ ⁻¹ᵁ W := ⟨hsT, hsW⟩
  obtain ⟨g, hg, hsg⟩ := hT.exists_basicOpen_le (V := T ⊓ σ ⁻¹ᵁ W)
    ⟨s, hsTW⟩ hsT
  let U : S.Opens := S.basicOpen g
  let a : Γ(X, W) := (f.appLE T W hWT).hom g
  let V : X.Opens := X.basicOpen a
  have hUaff : IsAffineOpen U := hT.basicOpen g
  have hVaff : IsAffineOpen V := hW.basicOpen a
  have hVeq : V = W ⊓ f ⁻¹ᵁ U := Scheme.basicOpen_appLE f _ _ hWT g
  have hVU : V ≤ f ⁻¹ᵁ U := by rw [hVeq]; exact inf_le_right
  have hsU : s ∈ U := hsg
  have hUV : U ≤ σ ⁻¹ᵁ V :=
    basicOpen_le_preimage_basicOpen_appLE f σ hσ hWT g fun y hy => (hg hy).2
  let A := Γ(S, U)
  let B := Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let A₀ := Γ(S, T)
  let B₀ := Γ(X, W)
  have hVW : V ≤ W := Scheme.basicOpen_le X a
  have hTV : V ≤ f ⁻¹ᵁ T := hVW.trans hWT
  let : Algebra A₀ B₀ := (f.appLE T W hWT).hom.toAlgebra
  let : Algebra B₀ B := (X.presheaf.map (homOfLE hVW).op).hom.toAlgebra
  let : Algebra A₀ B := (f.appLE T V hTV).hom.toAlgebra
  have hres : f.appLE T W hWT ≫ X.presheaf.map (homOfLE hVW).op =
      f.appLE T V hTV := Scheme.Hom.appLE_map f hWT (homOfLE hVW).op
  have : IsScalarTower A₀ B₀ B := isScalarTower_of_hom_comp_eq _ _ _ hres
  have : IsLocalization.Away a B := hW.isLocalization_basicOpen a
  have hSmooth₀ : Algebra.Smooth A₀ B₀ := RingHom.smooth_algebraMap.mp hsmoothRing
  have : Algebra.Smooth B₀ B := Algebra.Smooth.of_isLocalization_Away a
  have hSmooth₁ : Algebra.Smooth A₀ B := Algebra.Smooth.comp A₀ B₀ B
  have hUT : U ≤ T := fun y hy => (hg hy).1
  let : Algebra A₀ A := (S.presheaf.map (homOfLE hUT).op).hom.toAlgebra
  have : IsLocalization.Away g A := hT.isLocalization_basicOpen g
  have hmap : S.presheaf.map (homOfLE hUT).op ≫ f.appLE U V hVU = f.appLE T V hTV :=
    Scheme.Hom.map_appLE f hVU (homOfLE hUT).op
  have : IsScalarTower A₀ A B := isScalarTower_of_hom_comp_eq _ _ _ hmap
  exact ⟨U, V, hUaff, hVaff, hsU, hUV hsU, hVU, hUV,
    Algebra.Smooth.localization_base (.powers g)⟩

/-- At a smooth point of a section, there are compatible affine open neighbourhoods on which the
conormal module is free and the completion is a formal power series algebra over the base. -/
@[stacks 05D9]
public theorem exists_affineOpens_free_conormal_powerSeries
    {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (s : S)
    (hsmooth : InfinitesimalLifting.SmoothAt f (σ s)) :
    ∃ (U : S.Opens) (V : X.Opens) (_ : IsAffineOpen U)
      (_ : IsAffineOpen V) (_ : s ∈ U) (_ : σ s ∈ V)
      (hVU : V ≤ f ⁻¹ᵁ U) (hUV : U ≤ σ ⁻¹ᵁ V),
      let A := Γ(S, U)
      let B := Γ(X, V)
      letI : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
      ∃ (sectionHom : B →ₐ[A] A),
        sectionHom.toRingHom = (σ.appLE V U hUV).hom ∧
        (letI : Algebra B A := sectionHom.toAlgebra
         Module.Free A (RingHom.ker sectionHom.toRingHom).Cotangent) ∧
        (letI : Algebra B A := sectionHom.toAlgebra
         Nonempty (AdicCompletion (RingHom.ker sectionHom.toRingHom) B ≃ₐ[A]
           MvPowerSeries (Fin (Module.finrank A
             (RingHom.ker sectionHom.toRingHom).Cotangent)) A)) := by
  obtain ⟨U, V, hUaff, hVaff, hsU, hsV, hVU, hUV, hSm⟩ :=
    exists_affineOpens_smooth f σ hσ s hsmooth
  let A := Γ(S, U)
  let B := Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let sectionHom : B →ₐ[A] A := Scheme.Hom.sectionAlgHom f σ hσ U V hVU hUV
  let : Algebra B A := sectionHom.toAlgebra
  have hSmoothAB : Algebra.Smooth A B := hSm
  let J := RingHom.ker sectionHom.toRingHom
  let M := J.Cotangent
  have hcp := conormal_finite_projective sectionHom hSmoothAB
  have : Module.Finite A M := hcp.1
  have : Module.Projective A M := hcp.2
  have : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  let p : Ideal A := (hUaff.primeIdealOf ⟨s, hsU⟩).asIdeal
  have : p.IsPrime := (hUaff.primeIdealOf ⟨s, hsU⟩).isPrime
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_projective_of_isLocalRing
  obtain ⟨h, hh, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  let U' : S.Opens := S.basicOpen h
  let b : Γ(X, V) := (f.appLE U V hVU).hom h
  let V' : X.Opens := X.basicOpen b
  have hU'aff : IsAffineOpen U' := hUaff.basicOpen h
  have hV'aff : IsAffineOpen V' := hVaff.basicOpen b
  have hV'eq : V' = V ⊓ f ⁻¹ᵁ U' := Scheme.basicOpen_appLE f _ _ hVU h
  have hVU' : V' ≤ f ⁻¹ᵁ U' := by rw [hV'eq]; exact inf_le_right
  have hU'V' : U' ≤ σ ⁻¹ᵁ V' :=
    basicOpen_le_preimage_basicOpen_appLE f σ hσ hVU h fun y hy =>
      hUV (Scheme.basicOpen_le S h hy)
  have hsU' : s ∈ U' := mem_basicOpen_of_notMem_primeIdealOf hUaff ⟨s, hsU⟩ h hh
  have hsV' : σ s ∈ V' := hU'V' hsU'
  let A' := Γ(S, U')
  let B' := Γ(X, V')
  let : Algebra A' B' := (f.appLE U' V' hVU').hom.toAlgebra
  let sectionHom' : B' →ₐ[A'] A' := Scheme.Hom.sectionAlgHom f σ hσ U' V' hVU' hU'V'
  have hV'V : V' ≤ V := Scheme.basicOpen_le X b
  have hU'U : U' ≤ U := Scheme.basicOpen_le S h
  have hV'base : V' ≤ f ⁻¹ᵁ U := hV'V.trans hVU
  let : Algebra B B' := (X.presheaf.map (homOfLE hV'V).op).hom.toAlgebra
  let : Algebra A B' := (f.appLE U V' hV'base).hom.toAlgebra
  have hres' : f.appLE U V hVU ≫ X.presheaf.map (homOfLE hV'V).op =
      f.appLE U V' hV'base := Scheme.Hom.appLE_map f hVU (homOfLE hV'V).op
  have : IsScalarTower A B B' := isScalarTower_of_hom_comp_eq _ _ _ hres'
  have : IsLocalization.Away b B' := hVaff.isLocalization_basicOpen b
  have : Algebra.Smooth B B' := Algebra.Smooth.of_isLocalization_Away b
  have hSmoothABbase : Algebra.Smooth A B' := Algebra.Smooth.comp A B B'
  let : Algebra A A' := (S.presheaf.map (homOfLE hU'U).op).hom.toAlgebra
  have : IsLocalization.Away h A' := hUaff.isLocalization_basicOpen h
  have hmap' : S.presheaf.map (homOfLE hU'U).op ≫ f.appLE U' V' hVU' =
      f.appLE U V' hV'base := Scheme.Hom.map_appLE f hVU' (homOfLE hU'U).op
  have : IsScalarTower A A' B' := isScalarTower_of_hom_comp_eq _ _ _ hmap'
  have hSmoothAB' : Algebra.Smooth A' B' := Algebra.Smooth.localization_base (.powers h)
  have hσres :
      sectionHom'.toRingHom.comp (X.presheaf.map (homOfLE hV'V).op).hom =
        (S.presheaf.map (homOfLE hU'U).op).hom.comp sectionHom.toRingHom :=
    appLE_restrict_comm_hom σ hUV hU'V' hU'U hV'V
  have hsub : Submonoid.map sectionHom.toRingHom (.powers b) = .powers h :=
    map_powers_eq sectionHom h
  let J' : Ideal B' := RingHom.ker sectionHom'.toRingHom
  have hker : J' = J.map (algebraMap B B') :=
    ker_eq_map_of_localized sectionHom.toRingHom sectionHom'.toRingHom b h hsub hσres
  let idealEquiv := Ideal.Cotangent.equivOfEq (J.map (algebraMap B B')) J' hker.symm
  let cotangentMapB := Ideal.localizedCotangentMap (.powers b) B' J
  let cotangentMapA := cotangentMapB.restrictScalars A
  let cotangentIsoA := idealEquiv.restrictScalars A
  let localizedCotangent : J.Cotangent →ₗ[A] J'.Cotangent :=
    cotangentIsoA.toLinearMap.comp cotangentMapA
  have : IsLocalizedModule (.powers h) localizedCotangent := by
    have : IsLocalizedModule (.powers b) cotangentMapB :=
      Ideal.isLocalizedModule_localizedCotangentMap (.powers b) B' J
    have : IsLocalizedModule (.powers h) cotangentMapA :=
      IsLocalizedModule.restrictScalars_powers (R := A) (A := B) h cotangentMapB
    infer_instance
  let cotangentEquiv : LocalizedModule.Away h M ≃ₗ[A] J'.Cotangent :=
    IsLocalizedModule.linearEquiv (.powers h) (LocalizedModule.mkLinearMap (.powers h) M)
      localizedCotangent
  let ringEquiv : Localization (.powers h) ≃ₐ[A] A' :=
    IsLocalization.algEquiv (.powers h) (Localization (.powers h)) A'
  let : Algebra A' (Localization (.powers h)) := ringEquiv.symm.toRingHom.toAlgebra
  let : Module A' (LocalizedModule.Away h M) :=
    Module.compHom (LocalizedModule.Away h M) (algebraMap A' (Localization (.powers h)))
  have : IsScalarTower A A' (Localization (.powers h)) :=
    IsScalarTower.of_algebraMap_eq fun x => (ringEquiv.symm.commutes x).symm
  have : IsScalarTower A' (Localization (.powers h)) (LocalizedModule.Away h M) :=
    IsScalarTower.of_compHom (R := A') (A := Localization (.powers h))
      (M := LocalizedModule.Away h M)
  let : IsScalarTower A A' (LocalizedModule.Away h M) :=
    isScalarTower_of_tower_smul (Localization (.powers h))
  have hfreeA' : Module.Free A' (LocalizedModule.Away h M) :=
    free_of_ringEquiv ringEquiv.toRingEquiv (fun r x => by
      change r • x = ringEquiv.symm (ringEquiv r) • x
      rw [ringEquiv.symm_apply_apply]) hfree
  have hfreeJ' : Module.Free A' J'.Cotangent := by
    let cotangentEquiv' := cotangentEquiv.extendScalarsOfIsLocalization (.powers h) A'
    exact Module.Free.of_equiv' hfreeA' cotangentEquiv'
  refine ⟨U', V', hU'aff, hV'aff, hsU', hsV', hVU', hU'V', sectionHom', rfl, ?_⟩
  let : Algebra B' A' := sectionHom'.toAlgebra
  exact ⟨hfreeJ', adicCompletion_algEquiv_mvPowerSeries sectionHom' hSmoothAB' hfreeJ'⟩

end AlgebraicGeometry
