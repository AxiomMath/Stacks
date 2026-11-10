module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.GenericPointCount
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.FiniteIndEtale
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.StrictHenselization
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.GenericPointCount
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.FiniteIndEtale

/-!
# The generic-separable-degree weighting

This file shows that the weighted fibre sums of the generic separable degree are locally
constant, first over affine and finite pieces and then in general, and concludes that the generic
separable degree is a weighting.

## Main results

* `AlgebraicGeometry.exists_weighting_genericSeparableDegree` produces the weighting and
  identifies each of its values with the generic separable degree.
-/

public section

open AlgebraicGeometry
open IsLocalRing
open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance] affineResidueFieldField
attribute [local instance] affineStalkAlgebra
attribute [local instance] affineStalkLocalization
attribute [local instance] affineStalkLocalRing
attribute [local instance] affineStalkAlgebraAtSchemePoint
attribute [local instance] affineSchemePoint_isPrime
attribute [local instance] affineStalkLocalizationAtSchemePoint
attribute [local instance] affineStalkLocalRingAtSchemePoint

private noncomputable def genericFiberCount
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (prime : Ideal A) [prime.IsPrime] : ℕ :=
  Nat.card ((prime.ResidueField ⊗[A] B) →ₐ[prime.ResidueField]
    AlgebraicClosure prime.ResidueField)

private theorem genericFiberCount_eq_of_residueFieldMap
    (A B Rsh : Type u) [CommRing A] [CommRing B] [CommRing Rsh]
    [Algebra A B] [Module.Finite A B] [Algebra A Rsh]
    (prime : Ideal Rsh) [prime.IsPrime]
    (K : Type u) [Field K] [Algebra prime.ResidueField K] [IsAlgClosed K] :
    genericFiberCount A B (prime.comap (algebraMap A Rsh)) =
      Nat.card ((prime.ResidueField ⊗[A] B) →ₐ[prime.ResidueField] K) := by
  let contracted := prime.comap (algebraMap A Rsh)
  let : Algebra contracted.ResidueField prime.ResidueField :=
    (Ideal.ResidueField.map contracted prime (algebraMap A Rsh) rfl).toAlgebra
  let : IsScalarTower A contracted.ResidueField prime.ResidueField :=
    .of_algebraMap_eq fun value =>
      (Ideal.ResidueField.map_algebraMap contracted prime (algebraMap A Rsh) rfl value).symm
  let : Algebra contracted.ResidueField K :=
    ((algebraMap prime.ResidueField K).comp
      (algebraMap contracted.ResidueField prime.ResidueField)).toAlgebra
  let : IsScalarTower contracted.ResidueField prime.ResidueField K :=
    .of_algebraMap_eq' rfl
  let : Algebra A K := ((algebraMap prime.ResidueField K).comp
    (algebraMap A prime.ResidueField)).toAlgebra
  let : IsScalarTower A prime.ResidueField K := .of_algebraMap_eq' rfl
  let : IsScalarTower A contracted.ResidueField K :=
    IsScalarTower.to₁₂₄ A contracted.ResidueField prime.ResidueField K
  change Nat.card ((contracted.ResidueField ⊗[A] B) →ₐ[contracted.ResidueField]
    AlgebraicClosure contracted.ResidueField) = _
  rw [algHom_card_eq_of_isAlgClosed contracted.ResidueField _
    (AlgebraicClosure contracted.ResidueField) K]
  exact (Nat.card_congr (AlgHom.liftEquiv A contracted.ResidueField B K)).symm.trans
    (Nat.card_congr (AlgHom.liftEquiv A prime.ResidueField B K))

private theorem isOpen_irreducibleComponent_of_unique
    {T : Type*} [TopologicalSpace T]
    (hfinite : (irreducibleComponents T).Finite)
    (hunique : ∀ x : T, ∃! Z : irreducibleComponents T, x ∈ (Z : Set T))
    (Z : irreducibleComponents T) : IsOpen (Z : Set T) := by
  have heq : (Z : Set T)ᶜ = ⋃₀ (irreducibleComponents T \ {(Z : Set T)}) := by
    ext x
    constructor
    · intro hx
      obtain ⟨W, hxW, _⟩ := hunique x
      refine Set.mem_sUnion.mpr ⟨W, ⟨W.2, ?_⟩, hxW⟩
      simp only [Set.mem_singleton_iff]
      intro hWZ
      exact hx (hWZ ▸ hxW)
    · rintro ⟨W, ⟨hW, hWZ⟩, hxW⟩ hxZ
      obtain ⟨C, _, hC⟩ := hunique x
      have hWC : (⟨W, hW⟩ : irreducibleComponents T) = C := hC _ hxW
      have hZC : Z = C := hC _ hxZ
      have hWZ' : W = (Z : Set T) := congrArg Subtype.val (hWC.trans hZC.symm)
      exact hWZ (Set.mem_singleton_iff.mpr hWZ')
  rw [← isClosed_compl_iff, heq]
  exact hfinite.sdiff.isClosed_sUnion
    (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)

private theorem isLocallyConstant_of_constant_on_irreducibleComponents
    {T D : Type*} [TopologicalSpace T]
    (hfinite : (irreducibleComponents T).Finite)
    (hunique : ∀ x : T, ∃! Z : irreducibleComponents T, x ∈ (Z : Set T))
    (value : T → D)
    (hvalue : ∀ (Z : irreducibleComponents T) (x y : T),
      x ∈ (Z : Set T) → y ∈ (Z : Set T) → value x = value y) :
    IsLocallyConstant value := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨Z, hxZ, _⟩ := hunique x
  exact Filter.mem_of_superset
    ((isOpen_irreducibleComponent_of_unique hfinite hunique Z).mem_nhds hxZ)
    (fun y hy => hvalue Z y x hy hxZ)

private theorem minimalPrime_isPrime (A : Type u) [CommRing A]
    (prime : minimalPrimes A) : prime.1.IsPrime :=
  prime.2.isPrime

attribute [local instance] minimalPrime_isPrime

private theorem weightedFiberSum_eq_genericFiberCount
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (hY : IsGeometricallyUnibranch (Spec (.of A)))
    (point : PrimeSpectrum A) :
    ∃ prime : minimalPrimes A,
      prime.1 ≤ point.asIdeal ∧
      separableDegreeWeightedFiberSum
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (fun source => (genericSeparableDegree
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) hY source : ℤ)) point =
        (genericFiberCount A B prime.1 : ℤ) := by
  let localRing : Type u := (Spec (.of A)).presheaf.stalk point
  let : IsLocalRing localRing := inferInstanceAs
    (IsLocalRing ((Spec (.of A)).presheaf.stalk point))
  let closure := SeparableClosure (maximalIdeal localRing).ResidueField
  obtain ⟨Rsh, _, _, _, ⟨hRsh⟩⟩ := exists_strictHenselization localRing closure
  let := hRsh.henselian
  let : Algebra A Rsh := ((algebraMap localRing Rsh).comp
    (algebraMap A localRing)).toAlgebra
  let : IsScalarTower A localRing Rsh := .of_algebraMap_eq' rfl
  obtain ⟨prime, hprime, _⟩ := existsUnique_minimalPrime_of_strictHenselization
    localRing closure Rsh hRsh
    ((isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).mpr (hY point))
  let : prime.IsPrime := hprime.isPrime
  let contracted := prime.comap (algebraMap A Rsh)
  have hind : StacksDraft.IndEtale A Rsh :=
    StacksDraft.indEtale_comp (StacksDraft.indEtale_atPrime point.asIdeal)
      hRsh.isFilteredColimitEtale
  let : Algebra.WeaklyEtale A Rsh := weaklyEtale_of_indEtale hind
  have hcontracted : contracted ∈ minimalPrimes A := minimalPrime_comap_of_flat prime hprime
  refine ⟨⟨contracted, hcontracted⟩, ?_, ?_⟩
  · let := hRsh.isLocalHom
    have hmax : (maximalIdeal Rsh).comap (algebraMap A Rsh) = point.asIdeal := by
      rw [IsScalarTower.algebraMap_eq A localRing Rsh, ← Ideal.comap_comap,
        maximalIdeal_comap]
      exact IsLocalization.AtPrime.under_maximalIdeal localRing point.asIdeal
    rw [← hmax]
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  · rw [weightedFiberSum_eq_of_affine_strictHenselization
      A B hY point closure Rsh hRsh prime hprime (AlgebraicClosure prime.ResidueField)]
    exact congrArg (fun value : ℕ => (value : ℤ))
      (genericFiberCount_eq_of_residueFieldMap A B Rsh prime
        (AlgebraicClosure prime.ResidueField)).symm

private theorem existsUnique_irreducibleComponent_of_etale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g]
    (hY : IsGeometricallyUnibranch Y) (x : X) :
    ∃! Z : irreducibleComponents X, x ∈ (Z : Set X) := by
  let U : EtaleNeighborhood Y (g x) :=
    { scheme := X, point := x, toBase := g, map_point := rfl }
  exact (isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent Y (g x)).mp
    (hY (g x)) U

private theorem isGeometricallyUnibranch_of_etale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g]
    (hY : IsGeometricallyUnibranch Y) :
    IsGeometricallyUnibranch X := by
  intro point
  apply (isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent X point).mpr
  intro neighborhood
  let composite : EtaleNeighborhood Y (g point) :=
    { scheme := neighborhood.scheme
      point := neighborhood.point
      toBase := neighborhood.toBase ≫ g
      map_point := by simp [neighborhood.map_point] }
  exact (isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent Y (g point)).mp
    (hY (g point)) composite

private theorem minimalPrime_eq_of_unique_irreducibleComponent
    (A : Type u) [CommRing A]
    (hunique : ∀ point : PrimeSpectrum A,
      ∃! component : irreducibleComponents (PrimeSpectrum A),
        point ∈ (component : Set (PrimeSpectrum A)))
    (point : PrimeSpectrum A)
    (prime : minimalPrimes A) (hprime : prime.1 ≤ point.asIdeal)
    (component : irreducibleComponents (PrimeSpectrum A))
    (hcomponent : point ∈ (component : Set (PrimeSpectrum A))) :
    prime.1 = PrimeSpectrum.vanishingIdeal (component : Set (PrimeSpectrum A)) := by
  let componentPrime : irreducibleComponents (PrimeSpectrum A) :=
    ⟨PrimeSpectrum.zeroLocus (prime.1 : Set A),
      (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents).mpr
        (by rw [Ideal.IsPrime.radical inferInstance]; exact prime.2)⟩
  have hmem : point ∈ (componentPrime : Set (PrimeSpectrum A)) := hprime
  obtain ⟨unique, _, huniq⟩ := hunique point
  have heq : componentPrime = component := (huniq _ hmem).trans (huniq _ hcomponent).symm
  have hset := congrArg (fun comp : irreducibleComponents (PrimeSpectrum A) =>
    (comp : Set (PrimeSpectrum A))) heq
  rw [← hset]
  exact (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical prime.1).trans
    (Ideal.IsPrime.radical inferInstance) |>.symm

private theorem isLocallyConstant_weightedFiberSum_of_specFinite
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [IsLocallyNoetherian (Spec (.of A))]
    (hY : IsGeometricallyUnibranch (Spec (.of A))) :
    IsLocallyConstant (separableDegreeWeightedFiberSum
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (fun source => (genericSeparableDegree
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) hY source : ℤ))) := by
  let : AlgebraicGeometry.IsNoetherian (Spec (.of A)) := ⟨⟩
  have hunique : ∀ point : PrimeSpectrum A,
      ∃! component : irreducibleComponents (PrimeSpectrum A),
        point ∈ (component : Set (PrimeSpectrum A)) :=
    existsUnique_irreducibleComponent_of_etale (𝟙 (Spec (.of A))) hY
  apply isLocallyConstant_of_constant_on_irreducibleComponents
    finite_irreducibleComponents_of_isNoetherian hunique
  intro component point₁ point₂ hpoint₁ hpoint₂
  obtain ⟨prime₁, hprime₁, hsum₁⟩ := weightedFiberSum_eq_genericFiberCount A B hY point₁
  obtain ⟨prime₂, hprime₂, hsum₂⟩ := weightedFiberSum_eq_genericFiberCount A B hY point₂
  have heq : prime₁ = prime₂ := Subtype.ext
    ((minimalPrime_eq_of_unique_irreducibleComponent A hunique point₁
      prime₁ hprime₁ component hpoint₁).trans
      (minimalPrime_eq_of_unique_irreducibleComponent A hunique point₂
        prime₂ hprime₂ component hpoint₂).symm)
  cases heq
  exact hsum₁.trans hsum₂.symm

private theorem isLocallyConstant_of_affineCover
    {X : Scheme.{u}} {D : Type*} (value : X → D)
    (hvalue : ∀ index, IsLocallyConstant (value ∘ X.affineCover.f index)) :
    IsLocallyConstant value := by
  rw [IsLocallyConstant.iff_exists_open]
  intro point
  obtain ⟨index, lift, hlift⟩ := X.affineCover.exists_eq point
  obtain ⟨neighborhood, hopen, hliftmem, hconstant⟩ := (hvalue index).exists_open lift
  refine ⟨X.affineCover.f index '' neighborhood,
    (X.affineCover.f index).isOpenEmbedding.isOpenMap _ hopen,
    ⟨lift, hliftmem, hlift⟩, ?_⟩
  rintro image ⟨source, hsource, rfl⟩
  simpa [Function.comp_apply, hlift] using hconstant source hsource

private theorem isLocallyConstant_of_affine_irreducibleComponents
    {X : Scheme.{u}} [IsLocallyNoetherian X] {D : Type*}
    (hX : IsGeometricallyUnibranch X) (value : X → D)
    (hvalue : ∀ (index : X.affineCover.I₀)
      (component : irreducibleComponents (X.affineCover.X index))
      (point₁ point₂ : X.affineCover.X index),
      point₁ ∈ (component : Set (X.affineCover.X index)) →
      point₂ ∈ (component : Set (X.affineCover.X index)) →
      value (X.affineCover.f index point₁) = value (X.affineCover.f index point₂)) :
    IsLocallyConstant value := by
  apply isLocallyConstant_of_affineCover
  intro index
  let : IsLocallyNoetherian (X.affineCover.X index) :=
    isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f index)
  let : AlgebraicGeometry.IsNoetherian (X.affineCover.X index) := ⟨⟩
  exact isLocallyConstant_of_constant_on_irreducibleComponents
    finite_irreducibleComponents_of_isNoetherian
    (existsUnique_irreducibleComponent_of_etale (X.affineCover.f index) hX) _ (hvalue index)

private theorem genericSeparableDegree_eq_of_etale_square
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (π : U ⟶ V)
    (h : U ⟶ X) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] [Etale h] [Etale g]
    (hY : IsGeometricallyUnibranch Y) :
    (fun point : U => (genericSeparableDegree f hY (h point) : ℤ)) =
      fun point =>
        (genericSeparableDegree π (isGeometricallyUnibranch_of_etale g hY) point : ℤ) := by
  funext point
  let R := Y.presheaf.stalk (f (h point))
  let S := X.presheaf.stalk (h point)
  let R' := V.presheaf.stalk (π point)
  let S' := U.presheaf.stalk point
  have hpoint : f (h point) = g (π point) :=
    congrArg (fun morphism : U ⟶ Y => morphism point) comm
  let equality : Y.presheaf.stalk (f (h point)) ⟶ Y.presheaf.stalk (g (π point)) :=
    (Y.presheaf.stalkCongr (.of_eq hpoint)).hom
  let homR : R →+* R' := (g.stalkMap (π point)).hom.comp equality.hom
  let : Algebra R S := (f.stalkMap (h point)).hom.toAlgebra
  let : Algebra R R' := homR.toAlgebra
  let : Algebra S S' := (h.stalkMap point).hom.toAlgebra
  let : Algebra R' S' := (π.stalkMap point).hom.toAlgebra
  let : Algebra R S' := ((h.stalkMap point).hom.comp (f.stalkMap (h point)).hom).toAlgebra
  let : IsScalarTower R S S' := .of_algebraMap_eq' rfl
  have hstalk : (h.stalkMap point).hom.comp (f.stalkMap (h point)).hom =
      (π.stalkMap point).hom.comp homR := by
    have hmaps := Scheme.Hom.stalkMap_congr_hom (h ≫ f) (π ≫ g) comm point
    simp only [Scheme.Hom.stalkMap_comp] at hmaps
    have hmaps' := congrArg CommRingCat.Hom.hom hmaps
    simp only [CommRingCat.hom_comp] at hmaps'
    exact hmaps'
  let : IsScalarTower R R' S' := .of_algebraMap_eq' hstalk
  let : IsLocalHom equality.hom := inferInstance
  let : IsLocalHom homR := RingHom.isLocalHom_comp _ _
  let : IsLocalHom (algebraMap R R') := inferInstanceAs (IsLocalHom homR)
  let : IsLocalHom (algebraMap R S) :=
    inferInstanceAs (IsLocalHom (f.stalkMap (h point)).hom)
  let : IsLocalHom (algebraMap S S') :=
    inferInstanceAs (IsLocalHom (h.stalkMap point).hom)
  let : IsLocalHom (algebraMap R' S') :=
    inferInstanceAs (IsLocalHom (π.stalkMap point).hom)
  let : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f (h point)
  let : Algebra.QuasiFinite R S := (f.quasiFiniteAt (h point)).toAlgebra
  let : Algebra.EssFiniteType R' S' := LocallyOfFiniteType.stalkMap π point
  let : Algebra.QuasiFinite R' S' := (π.quasiFiniteAt point).toAlgebra
  let : Algebra.FormallyUnramified S S' := FormallyUnramified.stalkMap h point
  let : Algebra.EssFiniteType S S' := LocallyOfFiniteType.stalkMap h point
  let : Algebra.IsSeparable (ResidueField S) (ResidueField S') := inferInstance
  let : Algebra.EssFiniteType R R' :=
    RingHom.EssFiniteType.respectsIso.2 (g.stalkMap (π point)).hom
      (CategoryTheory.asIso equality).commRingCatIsoToRingEquiv
      (LocallyOfFiniteType.stalkMap g (π point))
  let : Algebra.FormallyUnramified R R' :=
    RingHom.FormallyUnramified.respectsIso.2 (g.stalkMap (π point)).hom
      (CategoryTheory.asIso equality).commRingCatIsoToRingEquiv
      (FormallyUnramified.stalkMap g (π point))
  let : Algebra.IsSeparable (ResidueField R) (ResidueField R') := inferInstance
  have hindR : StacksDraft.IndEtale R R' :=
    indEtale_respectsIso.2 (g.stalkMap (π point)).hom
      (CategoryTheory.asIso equality).commRingCatIsoToRingEquiv
      (indEtale_stalkMap g (π point))
  exact congrArg (fun degree : ℕ => (degree : ℤ)) <| genericPointCount_eq_of_indEtale
    ((isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing R).mpr (hY (f (h point))))
    ((isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing R').mpr
      (isGeometricallyUnibranch_of_etale g hY (π point)))
    hindR (indEtale_stalkMap h point)

private theorem isLocallyConstant_weightedFiberSum_of_isAffine
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (π : U ⟶ V)
    [IsFinite π] [IsLocallyNoetherian V]
    (hV : IsGeometricallyUnibranch V) :
    IsLocallyConstant (separableDegreeWeightedFiberSum π
      (fun point => (genericSeparableDegree π hV point : ℤ))) := by
  let A := Γ(V, ⊤)
  let B := Γ(U, ⊤)
  let : Algebra A B := π.appTop.hom.toAlgebra
  let affineMap := Spec.map π.appTop
  have hmap : affineMap = U.isoSpec.inv ≫ π ≫ V.isoSpec.hom := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality π]
    simp [affineMap]
  let : IsFinite affineMap := by rw [hmap]; infer_instance
  let : Module.Finite A B := (IsFinite.SpecMap_iff π.appTop).mp inferInstance
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    change IsFinite affineMap
    infer_instance
  let : IsLocallyNoetherian (Spec A) :=
    isLocallyNoetherian_of_isOpenImmersion V.isoSpec.inv
  let hspec := isGeometricallyUnibranch_of_etale V.isoSpec.inv hV
  have comm : U.isoSpec.inv ≫ π = affineMap ≫ V.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality π).symm
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback
    π U.isoSpec.inv affineMap V.isoSpec.inv (IsPullback.of_horiz_isIso ⟨comm⟩)
    π.finite_preimage_singleton (fun point => (genericSeparableDegree π hV point : ℤ))
  have hdegree : (fun point => (genericSeparableDegree π hV point : ℤ)) ∘ U.isoSpec.inv = _ :=
    genericSeparableDegree_eq_of_etale_square π affineMap U.isoSpec.inv V.isoSpec.inv comm hV
  rw [hdegree] at hsum
  have hconstant := isLocallyConstant_weightedFiberSum_of_specFinite A B hspec
  change IsLocallyConstant (separableDegreeWeightedFiberSum affineMap
    (fun point => (genericSeparableDegree affineMap hspec point : ℤ))) at hconstant
  rw [← hsum] at hconstant
  have hcomposed := hconstant.comp_continuous V.isoSpec.hom.continuous
  simpa [Function.comp_def, ← Scheme.Hom.comp_apply] using hcomposed

open CategoryTheory.Limits in
private theorem isLocallyConstant_weightedFiberSum_of_affineFinite
    (haffine : ∀ {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
      (π : U ⟶ V) [IsFinite π] [IsLocallyNoetherian V]
      (hV : IsGeometricallyUnibranch V),
      IsLocallyConstant (separableDegreeWeightedFiberSum π
        (fun point => (genericSeparableDegree π hV point : ℤ))))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (hY : IsGeometricallyUnibranch Y) :
    IsLocallyConstant (separableDegreeWeightedFiberSum f
      (fun point => (genericSeparableDegree f hY point : ℤ))) := by
  apply isLocallyConstant_of_affineCover
  intro index
  let baseMap := Y.affineCover.f index
  let source := pullback f baseMap
  let projection : source ⟶ Y.affineCover.X index := pullback.snd f baseMap
  let inclusion : source ⟶ X := pullback.fst f baseMap
  let hV := isGeometricallyUnibranch_of_etale baseMap hY
  let : IsLocallyNoetherian (Y.affineCover.X index) :=
    isLocallyNoetherian_of_isOpenImmersion baseMap
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback
    f inclusion projection baseMap (IsPullback.of_hasPullback f baseMap)
    f.finite_preimage_singleton (fun point => (genericSeparableDegree f hY point : ℤ))
  rw [hsum]
  rw [Function.comp_def, genericSeparableDegree_eq_of_etale_square f projection inclusion
    baseMap pullback.condition hY]
  exact haffine projection hV

open CategoryTheory.Limits in
private theorem isWeighting_genericSeparableDegree_of_finite
    (hfinite : ∀ {U V : Scheme.{u}} (π : U ⟶ V) [IsFinite π]
      [IsLocallyNoetherian V] (hV : IsGeometricallyUnibranch V),
      IsLocallyConstant (separableDegreeWeightedFiberSum π
        (fun point => (genericSeparableDegree π hV point : ℤ))))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsLocallyNoetherian Y]
    (hY : IsGeometricallyUnibranch Y) :
    IsWeighting f (fun point => (genericSeparableDegree f hY point : ℤ)) := by
  intro U V inclusion finiteMap baseMap comm hbase hopen hfiniteMap
  let : Etale baseMap := hbase
  let : IsFinite finiteMap := hfiniteMap
  let : IsOpenImmersion (pullback.lift inclusion finiteMap comm) := hopen
  have hinclusion : inclusion = pullback.lift inclusion finiteMap comm ≫
      pullback.fst f baseMap := (pullback.lift_fst inclusion finiteMap comm).symm
  let : Etale inclusion := by rw [hinclusion]; infer_instance
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian baseMap
  change IsLocallyConstant (separableDegreeWeightedFiberSum finiteMap
    (fun point => (genericSeparableDegree f hY (inclusion point) : ℤ)))
  rw [genericSeparableDegree_eq_of_etale_square f finiteMap inclusion baseMap comm hY]
  exact hfinite finiteMap (isGeometricallyUnibranch_of_etale baseMap hY)

/-- **The generic-separable-degree weighting.** For `f : X ⟶ Y` locally quasi-finite and locally of
finite type over a geometrically unibranch locally Noetherian scheme `Y`, there is a weighting
`w` of `f` whose value at `x` is, for all compatible strict henselizations `Rsh` of `𝒪_{Y,f(x)}`
and `Ssh` of `𝒪_{X,x}`, every minimal prime `p` of `Rsh` and every algebraic closure `Kbar` of
`κ(p)`, the number of `κ(p)`-algebra maps `κ(p) ⊗[Rsh] Ssh → Kbar`. -/
@[stacks 0F3E, sga "4 XVII 6.2.6" "n(x) is a weighting"]
public theorem exists_weighting_genericSeparableDegree
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsLocallyNoetherian Y]
    (hY : IsGeometricallyUnibranch Y) :
    ∃ w : X → ℕ,
      IsWeighting f (fun x ↦ (w x : ℤ)) ∧
      ∀ (x : X)
        (κY : Type u) [Field κY]
        [Algebra (maximalIdeal (Y.presheaf.stalk (f x))).ResidueField κY]
        [IsSepClosure (maximalIdeal (Y.presheaf.stalk (f x))).ResidueField κY]
        (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh]
        [Algebra (Y.presheaf.stalk (f x)) Rsh]
        (_hRsh : Stacks.StrictHenselization.IsStrictHenselization
          (Y.presheaf.stalk (f x)) κY Rsh)
        (κX : Type u) [Field κX]
        [Algebra (maximalIdeal (X.presheaf.stalk x)).ResidueField κX]
        [IsSepClosure (maximalIdeal (X.presheaf.stalk x)).ResidueField κX]
        (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh]
        [Algebra (X.presheaf.stalk x) Ssh] [Algebra Rsh Ssh]
        [Algebra (Y.presheaf.stalk (f x)) Ssh]
        [IsScalarTower (Y.presheaf.stalk (f x)) Rsh Ssh]
        (_hSsh : Stacks.StrictHenselization.IsStrictHenselization
          (X.presheaf.stalk x) κX Ssh)
        (_hcomp : (algebraMap (Y.presheaf.stalk (f x)) Ssh) =
          (algebraMap (X.presheaf.stalk x) Ssh).comp (f.stalkMap x).hom)
        (p : Ideal Rsh) [p.IsPrime] (_hp : p ∈ minimalPrimes Rsh)
        (Kbar : Type u) [Field Kbar]
        [Algebra p.ResidueField Kbar] [IsAlgClosure p.ResidueField Kbar],
        w x = Nat.card (AlgHom p.ResidueField
          (TensorProduct Rsh p.ResidueField Ssh) Kbar) := by
  refine ⟨genericSeparableDegree f hY, ?_, ?_⟩
  · apply isWeighting_genericSeparableDegree_of_finite
    intro U V π _ _ hV
    apply isLocallyConstant_weightedFiberSum_of_affineFinite
    intro U V _ _ π _ _ hV
    exact isLocallyConstant_weightedFiberSum_of_isAffine π hV
  · intro x κY _ _ _ Rsh _ _ _ hRsh κX _ _ _ Ssh _ _ _ _ _ _ hSsh hcomp p _ hp
      Kbar _ _ _
    exact genericSeparableDegree_eq f hY x κY Rsh hRsh κX Ssh hSsh hcomp p hp Kbar

end AlgebraicGeometry
