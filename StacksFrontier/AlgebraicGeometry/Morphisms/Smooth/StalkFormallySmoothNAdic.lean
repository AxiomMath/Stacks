module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.FormallySmooth.CompleteLocalTransfer
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk

/-!
# Smoothness at a point through the adic formal smoothness of the stalk map

Let `f : X ⟶ Y` be locally of finite type over a locally Noetherian scheme. Then `f` is smooth at
a point `x` if and only if the map of local rings `𝒪_{Y, f x} → 𝒪_{X, x}` is formally smooth for
the topology of the maximal ideal of `𝒪_{X, x}`. On affine opens this is Tag 07VH, and the stalk
map is identified with the map of localizations by `IsAffineOpen.arrowStalkMapIso`.

The file also collects the bridges used to move adic formal smoothness between a morphism out of
the spectrum of a local ring and the local homomorphism it induces on stalks.

## Main results

* `RingHom.formallySmoothNAdic_ringEquiv_comp_iff`,
  `RingHom.formallySmoothNAdic_comp_ringEquiv_iff`: adic formal smoothness is invariant under an
  isomorphism of the target (carrying the ideal along) and of the source.
* `RingHom.formallySmoothNAdic_iff_of_arrowIso`: the maximal-ideal-adic form transports along an
  isomorphism of arrows of local rings in `CommRingCat`.
* `AlgebraicGeometry.smoothAt_iff_formallySmoothNAdic_stalkMap`: smoothness at a point is adic
  formal smoothness of the stalk map.
* `AlgebraicGeometry.exists_isLocalization_stalk_comp_stalkClosedPointTo`: for a local `Λ`-algebra
  `A` and an open immersion `Spec Λ ⟶ S`, the stalk of `S` at the image of the closed point of
  `Spec A` is a localization of `Λ`, compatibly with the map to `A`.
* `AlgebraicGeometry.stalkClosedPointTo_comp_eq`,
  `AlgebraicGeometry.stalkClosedPointTo_specMap_fromSpecStalk_comp`,
  `AlgebraicGeometry.stalkClosedPointTo_specMap_comp`: the local homomorphism induced by a
  composite out of the spectrum of a local ring, up to the identification of stalks at equal
  points.
* `AlgebraicGeometry.formallySmoothNAdic_stalkClosedPointTo_fromSpecStalk_comp_iff` and
  `AlgebraicGeometry.formallySmoothNAdic_stalkClosedPointTo_specMap_ringEquiv_comp_iff`: the
  two transports of adic formal smoothness of `Scheme.stalkClosedPointTo`.

## References

* [Stacks Project, Tag 07VH](https://stacks.math.columbia.edu/tag/07VH)
* [Stacks Project, Tag 07NI](https://stacks.math.columbia.edu/tag/07NI)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe t u v w w'

namespace RingHom

/-- Adic formal smoothness is invariant under an isomorphism `e : A ≃+* A'` of the target: `φ` is
formally smooth for the `n`-adic topology iff `e ∘ φ` is for the `e(n)`-adic topology. -/
theorem formallySmoothNAdic_ringEquiv_comp_iff {R : Type v} {A : Type w} {A' : Type w'}
    [CommRing R] [CommRing A] [CommRing A'] (φ : R →+* A) (e : A ≃+* A') (n : Ideal A) :
    FormallySmoothNAdic.{t} (e.toRingHom.comp φ) (n.map e.toRingHom) ↔
      FormallySmoothNAdic.{t} φ n := by
  refine ⟨fun h => FormallySmoothNAdic.of_arrowEquiv_of_map_eq (RingEquiv.refl R) e.symm ?_ ?_ h,
    fun h => FormallySmoothNAdic.of_arrowEquiv (RingEquiv.refl R) e rfl h⟩
  · ext a
    exact (e.symm_apply_apply (φ a)).symm
  · rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]

/-- Adic formal smoothness is invariant under an isomorphism `d : R' ≃+* R` of the source: `φ` is
formally smooth for the `n`-adic topology iff `φ ∘ d` is. -/
theorem formallySmoothNAdic_comp_ringEquiv_iff {R : Type v} {R' : Type w'} {A : Type w}
    [CommRing R] [CommRing R'] [CommRing A] (φ : R →+* A) (d : R' ≃+* R) (n : Ideal A) :
    FormallySmoothNAdic.{t} (φ.comp d.toRingHom) n ↔ FormallySmoothNAdic.{t} φ n := by
  refine ⟨fun h => FormallySmoothNAdic.of_arrowEquiv_of_map_eq d (RingEquiv.refl A) ?_
      (Ideal.map_id n) h,
    fun h => FormallySmoothNAdic.of_arrowEquiv_of_map_eq d.symm (RingEquiv.refl A) ?_
      (Ideal.map_id n) h⟩
  · ext a
    rfl
  · ext a
    exact congrArg φ (d.apply_symm_apply a)

/-- For maps of local rings, formal smoothness for the maximal-ideal-adic topology of the target
is invariant under isomorphism of arrows in `CommRingCat`. -/
theorem formallySmoothNAdic_iff_of_arrowIso {A B A' B' : CommRingCat.{v}} [IsLocalRing B]
    [IsLocalRing B'] {φ : A ⟶ B} {ψ : A' ⟶ B'} (e : Arrow.mk φ ≅ Arrow.mk ψ) :
    FormallySmoothNAdic.{t} φ.hom (maximalIdeal B) ↔
      FormallySmoothNAdic.{t} ψ.hom (maximalIdeal B') := by
  have key : ∀ {A B A' B' : CommRingCat.{v}} [IsLocalRing B] [IsLocalRing B'] {φ : A ⟶ B}
      {ψ : A' ⟶ B'}, (Arrow.mk φ ≅ Arrow.mk ψ) →
      FormallySmoothNAdic.{t} φ.hom (maximalIdeal B) →
        FormallySmoothNAdic.{t} ψ.hom (maximalIdeal B') := by
    intro A B A' B' _ _ φ ψ e h
    let eR : B ≃+* B' := (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
    exact FormallySmoothNAdic.of_arrowEquiv_of_map_eq
      (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv eR
      (RingHom.ext fun a => congrArg (fun k : A ⟶ B' => k a) (Arrow.w e.hom))
      (map_ringEquiv_maximalIdeal eR) h
  exact ⟨key e, key e.symm⟩

end RingHom

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be locally of finite type with `Y` locally Noetherian. Then `f` is smooth at
`x` iff the stalk map `𝒪_{Y, f x} → 𝒪_{X, x}` is formally smooth for the `𝔪_x`-adic topology. -/
theorem smoothAt_iff_formallySmoothNAdic_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) :
    InfinitesimalLifting.SmoothAt f x ↔
      RingHom.FormallySmoothNAdic.{u} (f.stalkMap x).hom (maximalIdeal (X.presheaf.stalk x)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, V) :=
    Algebra.FinitePresentation.of_finiteType.mp this
  let p := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm⟩
  have h1 : InfinitesimalLifting.SmoothAt f x ↔ (f.stalkMap x).hom.FormallySmooth :=
    ⟨fun h => InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x h,
      fun h => InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x h⟩
  refine h1.trans ((formallySmooth_stalkMap_iff U hU V hV hVU hxV).trans ?_)
  refine (Algebra.smoothAt_iff_isSmoothAt Γ(Y, U) Γ(X, V) q).symm.trans ?_
  refine (smoothAt_iff_formallySmoothNAdic_localization p q).trans ?_
  exact (RingHom.formallySmoothNAdic_iff_of_arrowIso
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV)).symm

/-- Let `Spec Λ ⟶ S` be an open immersion, `A` a local `Λ`-algebra and `s ∈ S` the image of the
closed point of `Spec A`. Some `c : Λ → 𝒪_{S, s}` makes `𝒪_{S, s}` the localization of `Λ` at
`p = 𝔪_A ∩ Λ`, and composed with the induced map `𝒪_{S, s} → A` it is the structure map. -/
theorem exists_isLocalization_stalk_comp_stalkClosedPointTo {S : Scheme.{u}} {Λ : Type u}
    [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ] {A : Type u} [CommRing A]
    [IsLocalRing A] [Algebra Λ A] :
    ∃ c : Λ →+* S.presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) (closedPoint (CommRingCat.of A))),
      (letI := c.toAlgebra;
        IsLocalization.AtPrime (S.presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) (closedPoint (CommRingCat.of A))))
          ((maximalIdeal A).comap (algebraMap Λ A))) ∧
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)).hom.comp
        c = algebraMap Λ A := by
  let ψ : CommRingCat.of Λ ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap Λ A)
  let t : Spec (.of Λ) := Spec.map ψ (closedPoint (CommRingCat.of A))
  let e : S.presheaf.stalk (iΛ t) ≅ (Spec (.of Λ)).presheaf.stalk t := asIso (iΛ.stalkMap t)
  let c₀ : CommRingCat.of Λ ⟶ (Spec (.of Λ)).presheaf.stalk t :=
    (Scheme.ΓSpecIso (.of Λ)).inv ≫ (Spec (.of Λ)).presheaf.germ ⊤ t trivial
  refine ⟨(c₀ ≫ e.inv).hom, ?_, ?_⟩
  · have : t.asIdeal.IsPrime := PrimeSpectrum.isPrime t
    let : Algebra Λ ((Spec (.of Λ)).presheaf.stalk t) := StructureSheaf.stalkAlgebra Λ t
    have hloc : IsLocalization.AtPrime ((Spec (.of Λ)).presheaf.stalk t) t.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk Λ t
    exact (IsLocalization.isLocalization_iff_of_ringEquiv t.asIdeal.primeCompl
      e.symm.commRingCatIsoToRingEquiv).mp hloc
  · have key : c₀ ≫ Scheme.stalkClosedPointTo (Spec.map ψ) = ψ := by
      show (Scheme.ΓSpecIso (.of Λ)).inv ≫ (Spec (.of Λ)).presheaf.germ ⊤
        (Spec.map ψ (closedPoint (CommRingCat.of A))) trivial ≫
          Scheme.stalkClosedPointTo (Spec.map ψ) = ψ
      rw [Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
    have hcomp : Scheme.stalkClosedPointTo (Spec.map ψ ≫ iΛ) =
        e.hom ≫ Scheme.stalkClosedPointTo (Spec.map ψ) :=
      Scheme.stalkClosedPointTo_comp _ _
    have h3 : (c₀ ≫ e.inv) ≫ e.hom ≫ Scheme.stalkClosedPointTo (Spec.map ψ) = ψ := by
      rw [Category.assoc, e.inv_hom_id_assoc, key]
    rw [hcomp]
    exact congrArg CommRingCat.Hom.hom h3

/-- The local homomorphism induced by a composite `m ≫ g` out of the spectrum of a local ring is
the stalk map of `g` at a point `x` equal to the image of the closed point, followed by the local
homomorphism induced by `m`, up to the identifications of stalks at equal points. -/
theorem stalkClosedPointTo_comp_eq {X Y : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    (m : Spec R ⟶ X) (g : X ⟶ Y) {x : X} (hm : m (closedPoint R) = x) :
    Scheme.stalkClosedPointTo (m ≫ g) =
      (Y.presheaf.stalkCongr (.of_eq (congrArg g hm))).hom ≫
        g.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hm.symm)).hom ≫
          Scheme.stalkClosedPointTo m := by
  subst hm
  have h1 : ∀ (Z : Scheme.{u}) (y : Z) (h : Inseparable y y),
      (Z.presheaf.stalkCongr h).hom = 𝟙 _ := fun Z y h => by
    rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  rw [Scheme.stalkClosedPointTo_comp, h1 X, Category.id_comp]
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (h1 Y _ _).symm)

/-- For a local homomorphism `ψ : 𝒪_{X, x} ⟶ R` and `g : X ⟶ Y`, the local homomorphism induced
by `Spec R ⟶ Spec 𝒪_{X, x} ⟶ X ⟶ Y` is `g.stalkMap x ≫ ψ`, up to the identification of stalks. -/
theorem stalkClosedPointTo_specMap_fromSpecStalk_comp {X Y : Scheme.{u}} {x : X}
    {R : CommRingCat.{u}} [IsLocalRing R] (ψ : X.presheaf.stalk x ⟶ R) [IsLocalHom ψ.hom]
    (g : X ⟶ Y) :
    Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk x ≫ g) =
      (Y.presheaf.stalkCongr (.of_eq (congrArg g
          (StacksDraft.ArtinApproximation.specMap_fromSpecStalk_closedPoint ψ)))).hom ≫
        g.stalkMap x ≫ ψ := by
  have hc := StacksDraft.ArtinApproximation.specMap_fromSpecStalk_closedPoint ψ
  have h := stalkClosedPointTo_comp_eq (Spec.map ψ ≫ X.fromSpecStalk x) g hc
  rw [StacksDraft.ArtinApproximation.stalkCongr_comp_stalkClosedPointTo ψ hc] at h
  have key : ∀ (m₁ m₂ : Spec R ⟶ Y), m₁ = m₂ → ∀ (y : Y) (h₁ : m₁ (closedPoint R) = y)
      (h₂ : m₂ (closedPoint R) = y) (k : Y.presheaf.stalk y ⟶ R),
      Scheme.stalkClosedPointTo m₂ = (Y.presheaf.stalkCongr (.of_eq h₂)).hom ≫ k →
        Scheme.stalkClosedPointTo m₁ = (Y.presheaf.stalkCongr (.of_eq h₁)).hom ≫ k := by
    rintro m₁ _ rfl y h₁ h₂ k hk
    exact hk
  exact key _ _ (Category.assoc _ _ _).symm (g x)
    (congrArg g hc) (congrArg g hc) _ h

/-- Adic formal smoothness of the local homomorphism induced by `Spec R ⟶ Spec 𝒪_{X, x} ⟶ X ⟶ Y`
is adic formal smoothness of `g.stalkMap x ≫ ψ`. -/
theorem formallySmoothNAdic_stalkClosedPointTo_fromSpecStalk_comp_iff {X Y : Scheme.{u}} {x : X}
    {R : CommRingCat.{u}} [IsLocalRing R] (ψ : X.presheaf.stalk x ⟶ R) [IsLocalHom ψ.hom]
    (g : X ⟶ Y) :
    RingHom.FormallySmoothNAdic.{t}
        (Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk x ≫ g)).hom (maximalIdeal R) ↔
      RingHom.FormallySmoothNAdic.{t} (g.stalkMap x ≫ ψ).hom (maximalIdeal R) := by
  rw [stalkClosedPointTo_specMap_fromSpecStalk_comp]
  exact RingHom.formallySmoothNAdic_comp_ringEquiv_iff _
    (Iso.commRingCatIsoToRingEquiv _) _

/-- For a local homomorphism `φ : B' ⟶ B` of local rings and `m : Spec B' ⟶ Y`, the local
homomorphism induced by `Spec B ⟶ Spec B' ⟶ Y` is the one induced by `m` followed by `φ`, up to the
identification of stalks. -/
theorem stalkClosedPointTo_specMap_comp {Y : Scheme.{u}} {B' B : CommRingCat.{u}} [IsLocalRing B']
    [IsLocalRing B] (φ : B' ⟶ B) [IsLocalHom φ.hom] (m : Spec B' ⟶ Y) :
    Scheme.stalkClosedPointTo (Spec.map φ ≫ m) =
      (Y.presheaf.stalkCongr (.of_eq (congrArg m (Spec_closedPoint (f := φ))))).hom ≫
        Scheme.stalkClosedPointTo m ≫ φ := by
  rw [Scheme.stalkClosedPointTo_comp, InfinitesimalLifting.stalkClosedPointTo_specMap]
  exact (Scheme.Hom.stalkSpecializes_stalkMap_assoc m _ _ _ _).symm

/-- Adic formal smoothness of the local homomorphism induced by a morphism `Spec A' ⟶ Y` is
unchanged by precomposing with `Spec A ⟶ Spec A'` for a ring isomorphism `A' ≃+* A`. -/
theorem formallySmoothNAdic_stalkClosedPointTo_specMap_ringEquiv_comp_iff {Y : Scheme.{u}}
    {A A' : Type u} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (e : A' ≃+* A)
    (φ' : Spec (.of A') ⟶ Y) :
    RingHom.FormallySmoothNAdic.{t}
        (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ φ')).hom
        (maximalIdeal A) ↔
      RingHom.FormallySmoothNAdic.{t} (Scheme.stalkClosedPointTo φ').hom (maximalIdeal A') := by
  have : IsLocalHom (CommRingCat.ofHom e.toRingHom).hom :=
    ⟨fun a ha => by simpa using ha.map e.symm.toRingHom⟩
  rw [stalkClosedPointTo_specMap_comp, ← map_ringEquiv_maximalIdeal e]
  exact (RingHom.formallySmoothNAdic_comp_ringEquiv_iff _ (Iso.commRingCatIsoToRingEquiv _) _).trans
    (RingHom.formallySmoothNAdic_ringEquiv_comp_iff _ e _)

/-- **The smooth locus read on the completed local ring.** For `f : X ⟶ Y` locally of finite type
over a locally Noetherian scheme, a point `x` lies in the smooth locus of `f` exactly when the
local homomorphism `𝒪_{Y, f x} ⟶ 𝒪^∧_{X, x}` induced by `Spec 𝒪^∧_{X, x} ⟶ X ⟶ Y` is formally
smooth for the adic topology of `𝒪^∧_{X, x}`. -/
theorem mem_smoothLocus_iff_formallySmoothNAdic_completedLocalRing {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    haveI := Scheme.completedLocalRing_isLocal X x
    x ∈ f.smoothLocus ↔ RingHom.FormallySmoothNAdic.{u}
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Scheme.completedLocalRing X x))) ≫
          X.fromSpecStalk x ≫ f)).hom
      (maximalIdeal (Scheme.completedLocalRing X x)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Scheme.completedLocalRing_isLocal X x
  have hsm : x ∈ f.smoothLocus ↔ InfinitesimalLifting.SmoothAt f x :=
    ⟨fun h => InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x h,
      fun h => InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x h⟩
  rw [hsm, smoothAt_iff_formallySmoothNAdic_stalkMap]
  have : IsLocalHom (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (Scheme.completedLocalRing X x))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))))
  rw [formallySmoothNAdic_stalkClosedPointTo_fromSpecStalk_comp_iff]
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  exact RingHom.formallySmoothNAdic_algebraMap_adicCompletion_maximalIdeal_iff
    (Λ := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)

end AlgebraicGeometry

end
