module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal
public import StacksFrontier.RingTheory.Flat.AdicFiltration

/-!
# Flatness from infinitesimal neighbourhoods

Let `X ⟶ S` be a morphism of locally Noetherian schemes and `Z ⟶ S` a closed
subscheme. If every base change of the morphism to an infinitesimal neighbourhood
of `Z` is flat, then the morphism is flat over the underlying set of `Z`.

## Main results

* `AlgebraicGeometry.isFlatAt_of_flat_infinitesimalNeighbourhoods` is [Stacks, Tag 0D4G]: it
  detects flatness at points above a closed subscheme using all its infinitesimal
  neighbourhoods.

## Implementation notes

The infinitesimal neighbourhoods and their maps to the base are
`Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood` and
`Stacks.Thickenings.nthOrderToBase` ([Stacks, Tag 04EY]). Their base changes are
Mathlib's pullbacks, with the second projection giving the morphism to the infinitesimal
neighbourhood.

Flatness at a point is `AlgebraicGeometry.IsFlatAt` ([Stacks, Tag 02N3]), flatness of the stalk
map at that point.

The algebra is the local criterion in its adic-filtration form,
`Module.Flat.of_flat_quotient_pow` ([Stacks, Tag 0523]): for `R`, `S` Noetherian and `I ⊆ R` an
ideal, flatness of `S/IⁿS` over `R/Iⁿ` for all `n` gives flatness of `S` over `R` after
localizing on the closed set cut out by `I`. Here `R` and `S` are the stalks of the base and the
source, `I` is the kernel of the stalk map of the closed immersion, and the quotients are
identified with the stalks of the infinitesimal neighbourhoods; the hypothesis provides their
flatness through `AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`, which
presents the stalk of a fibre product as a localization of the tensor product of the stalks.

## References

* [Stacks Project, Tag 0D4G](https://stacks.math.columbia.edu/tag/0D4G)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private lemma ker_eq_comap_of_arrowIso
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R' →+* S')
    (e : Arrow.mk (CommRingCat.ofHom f) ≅ Arrow.mk (CommRingCat.ofHom g)) :
    RingHom.ker f = (RingHom.ker g).comap e.hom.left.hom := by
  have hcomp : g.comp e.hom.left.hom = e.hom.right.hom.comp f :=
    CommRingCat.hom_ext_iff.mp e.hom.w
  calc
    RingHom.ker f = RingHom.ker (e.hom.right.hom.comp f) := by
      symm
      exact RingHom.ker_equiv_comp f (asIso e.hom.right).commRingCatIsoToRingEquiv
    _ = RingHom.ker (g.comp e.hom.left.hom) := by rw [hcomp]
    _ = (RingHom.ker g).comap e.hom.left.hom := by
      ext x
      simp [RingHom.mem_ker]

private lemma ker_localRingHom_of_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap f) :
    RingHom.ker (Localization.localRingHom p q f hpq) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime p)) := by
  have hmap : Submonoid.map f p.primeCompl = q.primeCompl := by
    have hp : p.primeCompl = (q.comap f).primeCompl := by
      cases hpq
      rfl
    rw [hp]
    show Submonoid.map f (Submonoid.comap f q.primeCompl) = q.primeCompl
    exact Submonoid.map_comap_eq_of_surjective (f := f) hf q.primeCompl
  have : IsLocalization (Submonoid.map f p.primeCompl) (Localization.AtPrime q) := by
    rw [hmap]
    infer_instance
  show RingHom.ker (IsLocalization.map (Localization.AtPrime q) f
    (Localization.le_comap_primeCompl_iff.mpr (ge_of_eq hpq))) = _
  exact IsLocalization.ker_map (Localization.AtPrime q) f hmap

private noncomputable def lift_to_idealPower_subscheme
    {T Z : Scheme.{u}} (g : Z ⟶ T) [IsClosedImmersion g] (n : ℕ) :
    Z ⟶ (g.ker ^ (n + 1)).subscheme :=
  IsClosedImmersion.lift (g.ker ^ (n + 1)).subschemeι g (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply Scheme.IdealSheafData.le_def.mpr
    intro U
    exact Ideal.pow_le_self (by omega))

private lemma lift_to_idealPower_subscheme_base
    {T Z : Scheme.{u}} (g : Z ⟶ T) [IsClosedImmersion g]
    (n : ℕ) (z : Z) :
    (g.ker ^ (n + 1)).subschemeι (lift_to_idealPower_subscheme g n z) = g z :=
  congrArg (fun k : Z ⟶ T => k z)
    (IsClosedImmersion.lift_fac (g.ker ^ (n + 1)).subschemeι g _)

private lemma ker_stalkMap_eq_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (x : X) (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    RingHom.ker (f.stalkMap x).hom =
      (f.ker.ideal ⟨U, hU⟩).map (Y.presheaf.germ U (f x) hx).hom := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let p := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let a := (f.appLE U V le_rfl).hom
  have hpq : p = q.comap a :=
    (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hx)).symm
  have ha : Function.Surjective a := by
    dsimp only [a, V]
    rw [Scheme.Hom.appLE_eq_app]
    exact f.app_surjective U hU
  have hka : RingHom.ker a = f.ker.ideal ⟨U, hU⟩ := by
    dsimp only [a, V]
    rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.ker_apply]
  let e := IsAffineOpen.arrowStalkMapIso f U hU V hV le_rfl hx
  rw [ker_eq_comap_of_arrowIso (f.stalkMap x).hom
    (Localization.localRingHom p q a hpq) e,
    ker_localRingHom_of_surjective a ha p q hpq, hka]
  let eL := (asIso e.hom.left).commRingCatIsoToRingEquiv
  apply (Ideal.relIsoOfBijective e.hom.left.hom eL.bijective).symm.injective
  show Ideal.map e.hom.left.hom (Ideal.comap e.hom.left.hom _) =
    Ideal.map e.hom.left.hom _
  rw [Ideal.map_comap_of_surjective e.hom.left.hom eL.surjective, Ideal.map_map]
  congr 1
  let := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  have := hU.isLocalization_stalk ⟨f x, hx⟩
  ext r
  exact (IsLocalization.algEquiv p.primeCompl
    (Y.presheaf.stalk (f x)) (Localization.AtPrime p)).commutes r |>.symm

private lemma ker_stalkMap_congr_eq_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (x : X) (U : Y.Opens) (hU : IsAffineOpen U)
    (y : Y) (hy : y ∈ U) (h : y = f x) :
    RingHom.ker ((eqToHom (congrArg Y.presheaf.stalk h) ≫ f.stalkMap x).hom) =
      (f.ker.ideal ⟨U, hU⟩).map (Y.presheaf.germ U y hy).hom := by
  subst y
  simpa using ker_stalkMap_eq_map f x U hU hy

private theorem ker_subscheme_stalkMap_eq_pow
    {T Z : Scheme.{u}} (g : Z ⟶ T) [IsClosedImmersion g]
    (n : ℕ) (z : Z) (t : T) (h : t = g z) :
    RingHom.ker ((eqToHom (congrArg T.presheaf.stalk
      (h.trans (lift_to_idealPower_subscheme_base g n z).symm)) ≫
      ((g.ker ^ (n + 1)).subschemeι).stalkMap
        (lift_to_idealPower_subscheme g n z)).hom) =
      RingHom.ker ((eqToHom (congrArg T.presheaf.stalk h) ≫
        g.stalkMap z).hom) ^ (n + 1) := by
  obtain ⟨U, hU, ht, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := T) (x := t) (U := ⊤) (by simp)
  rw [ker_stalkMap_congr_eq_map _ _ U hU t ht
    (h.trans (lift_to_idealPower_subscheme_base g n z).symm),
    ker_stalkMap_congr_eq_map g z U hU t ht h]
  simp only [Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Ideal.map_pow]

private noncomputable def coborderRangeIso_of_isClosedImmersion
    {X S : Scheme.{u}} (i : X ⟶ S) [IsClosedImmersion i] :
    i.coborderRange.toScheme ≅ S := by
  have h : i.coborderRange = ⊤ := by
    apply SetLike.coe_injective
    change coborder (Set.range i) = Set.univ
    exact i.isClosedEmbedding.isClosed_range.coborder_eq
  have : IsIso i.coborderRange.ι := by
    rw [h]
    exact Iso.isIso_hom (Scheme.topIso S)
  exact asIso i.coborderRange.ι

private theorem flat_pullback_snd_of_targetIso
    {X S T S' : Scheme.{u}} (f : X ⟶ S) (e : S' ≅ S) (g : T ⟶ S')
    (hflat : Flat (pullback.snd f (g ≫ e.hom))) :
    Flat (pullback.snd (f ≫ e.inv) g) := by
  let f' : X ⟶ S' := f ≫ e.inv
  let t : T ⟶ S := g ≫ e.hom
  let m : pullback f' g ⟶ pullback f t :=
    pullback.lift (pullback.fst f' g) (pullback.snd f' g) (by
      calc
        pullback.fst f' g ≫ f = pullback.fst f' g ≫ f' ≫ e.hom := by
          simp [f', Category.assoc]
        _ = pullback.snd f' g ≫ g ≫ e.hom := pullback.condition_assoc e.hom
        _ = pullback.snd f' g ≫ t := rfl)
  let n : pullback f t ⟶ pullback f' g :=
    pullback.lift (pullback.fst f t) (pullback.snd f t) (by
      calc
        pullback.fst f t ≫ f' = pullback.fst f t ≫ f ≫ e.inv := rfl
        _ = pullback.snd f t ≫ t ≫ e.inv := pullback.condition_assoc e.inv
        _ = pullback.snd f t ≫ g := by simp [t, Category.assoc])
  have hm₁ : m ≫ pullback.fst f t = pullback.fst f' g := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f t = pullback.snd f' g := pullback.lift_snd _ _ _
  have hn₁ : n ≫ pullback.fst f' g = pullback.fst f t := pullback.lift_fst _ _ _
  have hn₂ : n ≫ pullback.snd f' g = pullback.snd f t := pullback.lift_snd _ _ _
  have hmn : m ≫ n = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [Category.assoc, hm₁, hm₂, hn₁, hn₂]
  have hnm : n ≫ m = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [Category.assoc, hm₁, hm₂, hn₁, hn₂]
  have : IsIso m := ⟨⟨n, hmn, hnm⟩⟩
  rw [← hm₂]
  exact Flat.comp m (pullback.snd f t)

private theorem flat_ringHom_of_flat_quotient_pow_local
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    (I : Ideal R)
    (hI : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S)
    (hflat : ∀ n : ℕ,
      Module.Flat (R ⧸ I ^ (n + 1))
        (S ⧸ (I ^ (n + 1) • (⊤ : Submodule R S)))) :
    Module.Flat R S := by
  have : IsLocalization.AtPrime S (IsLocalRing.maximalIdeal S) :=
    IsLocalization.self fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx
  have : IsLocalizedModule.AtPrime (IsLocalRing.maximalIdeal S)
      (LinearMap.id : S →ₗ[S] S) :=
    isLocalizedModule_id (IsLocalRing.maximalIdeal S).primeCompl S S
  exact Module.Flat.of_flat_quotient_pow I S hflat
    (IsLocalRing.maximalIdeal S) hI S LinearMap.id

private theorem flat_of_localized_tensor_after_surjective_left
    {A T C B : Type u} [CommRing A] [CommRing T] [CommRing C] [CommRing B]
    [IsLocalRing A] [IsLocalRing C]
    (qA : A →+* T) (hqA : Function.Surjective qA)
    (α : A →+* C) [IsLocalHom α]
    (φ : T →+* C) [Algebra T C]
    (hφ : φ = algebraMap T C) (hA : φ.comp qA = α)
    (M : Submonoid T) (hlocal : IsLocalization M C)
    (qB : B →+* T) (β : B →+* C) (hB : φ.comp qB = β)
    (hflat : RingHom.Flat β) : RingHom.Flat qB := by
  have : Nontrivial T := φ.domain_nontrivial
  have : IsLocalRing T := IsLocalRing.of_surjective' qA hqA
  have hφlocal : IsLocalHom φ := by
    refine ⟨fun t ht => ?_⟩
    obtain ⟨a, rfl⟩ := hqA t
    have ha : IsUnit (α a) := by rwa [← DFunLike.congr_fun hA a]
    exact RingHom.isUnit_map qA (IsLocalHom.map_nonunit (f := α) a ha)
  have := hlocal
  have hM : M ≤ IsUnit.submonoid T := by
    intro s hs
    have hφs : IsUnit (φ s) := by
      rw [hφ]
      exact IsLocalization.map_units C ⟨s, hs⟩
    exact (isUnit_map_iff φ s).mp hφs
  have : IsLocalization M T := IsLocalization.self hM
  have hφbij : Function.Bijective φ := IsLocalization.bijective M φ (by
    rw [RingHom.algebraMap_toAlgebra]
    simp [hφ])
  exact (RingHom.Flat.comp_iff_of_bijective_left hφbij).mp (by rwa [hB])

private theorem flat_quotient_of_flat_tensor
    {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
    [Algebra R S] [Algebra R Q]
    (I : Ideal R) (hQ : Function.Surjective (algebraMap R Q))
    (hker : RingHom.ker (algebraMap R Q) = I)
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.includeRight (A := S) (R := R) (B := Q)).toRingHom) :
    Module.Flat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) := by
  let e₀ := RingHom.quotientKerEquivOfSurjective (f := algebraMap R Q) hQ
  let eQring : (R ⧸ I) ≃+* Q := (Ideal.quotEquivOfEq hker.symm).trans e₀
  let eQ : (R ⧸ I) ≃ₐ[R] Q :=
    { eQring with commutes' := fun r => by simp [eQring, e₀] }
  let T₀ := TensorProduct R S (R ⧸ I)
  let T := TensorProduct R S Q
  let eTensor : T₀ ≃ₐ[S] T :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eQ
  have hright0 : RingHom.Flat
      (Algebra.TensorProduct.includeRight (A := S) (R := R) (B := R ⧸ I)).toRingHom := by
    have hcomp :
        (Algebra.TensorProduct.includeRight (A := S) (R := R) (B := Q)).toRingHom.comp
            eQ.toRingEquiv.toRingHom =
          eTensor.toRingEquiv.toRingHom.comp
            (Algebra.TensorProduct.includeRight (A := S) (R := R) (B := R ⧸ I)).toRingHom := by
      apply RingHom.ext
      intro x
      show 1 ⊗ₜ[R] eQ x = eTensor (1 ⊗ₜ[R] x)
      exact (Algebra.TensorProduct.map_tmul
        (AlgEquiv.refl : S ≃ₐ[S] S).toAlgHom eQ.toAlgHom 1 x).symm
    apply (RingHom.Flat.comp_iff_of_bijective_left eTensor.bijective).mp
    show RingHom.Flat (eTensor.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := S) (R := R) (B := R ⧸ I)).toRingHom)
    rw [← hcomp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective eQ.bijective) hflat
  let e := Algebra.TensorProduct.comm R S (R ⧸ I)
  have hleft : RingHom.Flat
      (algebraMap (R ⧸ I) (TensorProduct R (R ⧸ I) S)) := by
    convert RingHom.Flat.comp hright0 (RingHom.Flat.of_bijective e.bijective) using 1
    apply RingHom.ext
    intro r
    show r ⊗ₜ[R] 1 = e (1 ⊗ₜ[R] r)
    exact (Algebra.TensorProduct.comm_tmul R (1 : S) r).symm
  exact (Module.Flat.equiv_iff
    ((TensorProduct.quotTensorEquivQuotSMul S I).extendScalarsOfSurjective
      (S := R ⧸ I) Ideal.Quotient.mk_surjective)).mp (RingHom.flat_algebraMap_iff.mp hleft)

/-- The stalk map of a closed immersion, composed with a stalk identification, is surjective. -/
private theorem surjective_eqToHom_stalkMap
    {T S : Scheme.{u}} (g : T ⟶ S) [IsClosedImmersion g] (z : T) (s : S) (h : s = g z) :
    Function.Surjective (eqToHom (congrArg S.presheaf.stalk h) ≫ g.stalkMap z).hom :=
  (g.stalkMap_surjective _).comp
    (asIso (eqToHom (congrArg S.presheaf.stalk h))).commRingCatIsoToRingEquiv.surjective

private theorem flat_tensor_stalk_of_flat_pullback
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [IsClosedImmersion g]
    (hflat : Flat (pullback.snd f g)) (x : X) (z : T) (h : f x = g z) :
    let R := S.presheaf.stalk (f x)
    let A := X.presheaf.stalk x
    let B := T.presheaf.stalk z
    let : Algebra R A := (f.stalkMap x).hom.toAlgebra
    let : Algebra R B :=
      (eqToHom (congrArg S.presheaf.stalk h) ≫ g.stalkMap z).hom.toAlgebra
    RingHom.Flat (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom := by
  obtain ⟨w, rfl, rfl⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x z h
  dsimp only
  let R := S.presheaf.stalk (f ((pullback.fst f g) w))
  let A := X.presheaf.stalk ((pullback.fst f g) w)
  let B := T.presheaf.stalk ((pullback.snd f g) w)
  let C := (pullback f g).presheaf.stalk w
  let q := eqToHom (congrArg S.presheaf.stalk h) ≫
    g.stalkMap ((pullback.snd f g) w)
  let : Algebra R A := (f.stalkMap ((pullback.fst f g) w)).hom.toAlgebra
  let : Algebra R B := q.hom.toAlgebra
  obtain ⟨φ, hφA, hφB, M, hM⟩ := BaseChangeStalk.pullback_stalk_isLocalization f g w
  let : Algebra (TensorProduct R A B) C := φ.toAlgebra
  have hq : Function.Surjective q.hom := surjective_eqToHom_stalkMap g _ _ h
  let l : A →+* TensorProduct R A B := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* TensorProduct R A B := Algebra.TensorProduct.includeRight.toRingHom
  have hl : Function.Surjective l := Algebra.TensorProduct.includeLeft_surjective A A hq
  have hright : φ.comp r = ((pullback.snd f g).stalkMap w).hom := hφB
  exact flat_of_localized_tensor_after_surjective_left
    (A := A) (T := TensorProduct R A B) (C := C) (B := B)
    l hl ((pullback.fst f g).stalkMap w).hom φ rfl hφA M hM
    r ((pullback.snd f g).stalkMap w).hom hright
    ((Flat.iff_flat_stalkMap _).mp hflat w)

private theorem flat_stalkMap_of_flat_idealPower_pullbacks
    {X S Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (f : X ⟶ S) (g : Z ⟶ S) [IsClosedImmersion g]
    (hflat : ∀ n : ℕ, Flat (pullback.snd f (g.ker ^ (n + 1)).subschemeι))
    (x : X) (z : Z) (h : f x = g z) : (f.stalkMap x).hom.Flat := by
  let R := S.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let q := eqToHom (congrArg S.presheaf.stalk h) ≫ g.stalkMap z
  let I := RingHom.ker q.hom
  show Module.Flat R A
  apply flat_ringHom_of_flat_quotient_pow_local I
  · rw [Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top q.hom)).trans_eq
      (IsLocalRing.maximalIdeal_comap (f.stalkMap x).hom).symm
  · intro n
    let zn := lift_to_idealPower_subscheme g n z
    let j := (g.ker ^ (n + 1)).subschemeι
    have hn : f x = j zn := h.trans (lift_to_idealPower_subscheme_base g n z).symm
    let qn := eqToHom (congrArg S.presheaf.stalk hn) ≫ j.stalkMap zn
    let : Algebra R ((g.ker ^ (n + 1)).subscheme.presheaf.stalk zn) := qn.hom.toAlgebra
    exact flat_quotient_of_flat_tensor
      (Q := (g.ker ^ (n + 1)).subscheme.presheaf.stalk zn) (I ^ (n + 1))
      (surjective_eqToHom_stalkMap j zn _ hn)
      (ker_subscheme_stalkMap_eq_pow g n z (f x) h)
      (flat_tensor_stalk_of_flat_pullback f j (hflat n) x zn hn)

/-- Flatness over a closed subscheme can be checked on every infinitesimal
neighbourhood of that subscheme when the schemes are locally Noetherian. -/
@[stacks 0D4G]
theorem isFlatAt_of_flat_infinitesimalNeighbourhoods
    {X S Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (f : X ⟶ S) (i : Z ⟶ S) [IsClosedImmersion i]
    (hflat : ∀ n : ℕ, Flat (pullback.snd f (Stacks.Thickenings.nthOrderToBase i n)))
    (x : X) (hx : f x ∈ Set.range i) :
    IsFlatAt f.toLRSHom.toShHom x := by
  obtain ⟨z, hz⟩ := hx
  let e := coborderRangeIso_of_isClosedImmersion i
  let f' := f ≫ e.inv
  have hf : f' ≫ e.hom = f := by simp [f']
  have h : f' x = i.liftCoborder z := by
    apply e.hom.isOpenEmbedding.injective
    show (f' ≫ e.hom) x = (i.liftCoborder ≫ e.hom) z
    rw [hf]
    show f x = (i.liftCoborder ≫ i.coborderRange.ι) z
    rw [Scheme.Hom.liftCoborder_ι]
    exact hz.symm
  have hflat' (n : ℕ) :
      Flat (pullback.snd f' (i.liftCoborder.ker ^ (n + 1)).subschemeι) :=
    flat_pullback_snd_of_targetIso f e _ (hflat n)
  show (f.stalkMap x).hom.Flat
  rw [← hf, Scheme.Hom.stalkMap_comp]
  show ((f'.stalkMap x).hom.comp (e.hom.stalkMap (f' x)).hom).Flat
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective
      (asIso (e.hom.stalkMap (f' x))).commRingCatIsoToRingEquiv.bijective)
    (flat_stalkMap_of_flat_idealPower_pullbacks f' i.liftCoborder hflat' x z h)

end AlgebraicGeometry
