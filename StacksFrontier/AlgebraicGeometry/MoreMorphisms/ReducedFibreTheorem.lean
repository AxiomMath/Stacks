module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkIntegralClosureLocalization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreBaseIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizedSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReplacement
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTower

/-!
# The reduced fibre theorem

Let `A` be a Nagata Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat,
quasi-compact and locally of finite type.  **Then there is a finite extension `L / K` such that,
with `B` the integral closure of `A` in `L`, the normalization of `X ×_{Spec A} Spec B` is smooth
over `Spec B` at every generic point of every one of its fibres.**  This is Tag 09IL, and `X` is
assumed neither reduced nor normal nor affine.

The proof is the composition of its two paragraphs.  The first,
`AlgebraicGeometry.exists_finite_extension_dense_open_smooth_genericFibre_normalization`, replaces
`A` by the integral closure `B₀` of `A` in a finite extension `L₀ / K` and `X` by the
normalization `Y₀` of `X ×_{Spec A} Spec B₀`, so chosen that the generic fibre of
`Y₀ ⟶ Spec B₀` carries a dense open subscheme smooth over the residue field there; the new base
is again a Nagata Dedekind domain with fraction field `L₀`
(`AlgebraicGeometry.isDedekindDomain_isNagataRing_isFractionRing_integralClosure`) and the new
scheme is normal and again flat, quasi-compact and locally of finite type over it
(`AlgebraicGeometry.flat_locallyOfFiniteType_quasiCompact_normalization_pullback`).  The last
paragraph,
`AlgebraicGeometry.exists_finiteExtension_smoothAt_normalization_pullback_of_dense_open_smooth`,
then produces a further finite extension `L₁ / L₀` and the smoothness of the normalization of
`Y₀ ×_{Spec B₀} Spec (integralClosure B₀ L₁)` at every generic point of every fibre.

Three identifications turn that into the theorem.  The two normalized base changes are compared
by `AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower`, whose
`UniversallyOpen` hypothesis is
`AlgebraicGeometry.universallyOpen_specMap_algebraMap_integralClosure`: taking the normalized base
change twice along the tower `A ⟶ B₀ ⟶ B₁` is taking it once.  Across the resulting isomorphism —
one over `Spec B₁` — smoothness and the generic-point condition travel by
`InfinitesimalLifting.smoothAt_iso_hom_iff` and
`AlgebraicGeometry.mem_genericPoints_asFiber_iso_hom_iff`.  Finally the base so produced is
`integralClosure B₀ L₁` while the theorem names `integralClosure A L₁`: the same subring of `L₁`
by `integralClosure_eq_restrictScalars_of_isIntegral`, but a different *type*, so the conclusion
is carried along the ring isomorphism of the bases by
`AlgebraicGeometry.smoothAt_normalization_pullback_of_isIso_base`.

## Main results

* `exists_ringEquiv_integralClosure_of_isIntegral`: for a tower `R ⟶ B ⟶ L` with `B` integral
  over `R`, the integral closure of `R` in `L` and the integral closure of `B` in `L` are
  isomorphic as rings, compatibly with the maps from `R`.
* `AlgebraicGeometry.smoothAt_asFiber_genericPoints_normalization_pullback_of_tower`: the two
  finite extensions of the proof compose.
* `AlgebraicGeometry.exists_finiteExtension_smoothAt_asFiber_genericPoints_normalization_pullback`:
  Tag 09IL for a fraction field in the scheme's own universe, with the generic-point condition in
  its ambient form.
* `AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`:
  **Tag 09IL.**

## Implementation notes

The `A`-algebra structure on the extension is existentially quantified together with the witness
that it is the composite of `A ⟶ K ⟶ L`, rather than fixed as that composite: the integral
closure `integralClosure A L` depends on the structure, and every structure satisfying
`IsScalarTower A K L` has the same `algebraMap`, hence the same integral closure.  This is the
form in which the chain of lemmas leading here states its extensions.

The finiteness-of-irreducible-components witness is part of the existentially quantified data,
not a hypothesis on the conclusion. It has to appear at all because
`AlgebraicGeometry.Scheme.normalization` takes it as an explicit argument, so the normalization
cannot even be named without it; but it is a theorem here, not an assumption — the integral
closure of a Nagata Dedekind domain in a finite extension of its fraction field is Dedekind
(`AlgebraicGeometry.isDedekindDomain_integralClosure_of_isNagataRing`), hence Noetherian, so
`AlgebraicGeometry.finite_irreducibleComponents_isCompact_of_locallyOfFiniteType` supplies it.
Being a proposition, every choice names the same normalization, so a caller holding a different
witness can use the conclusion directly. The intermediate
`AlgebraicGeometry.exists_finiteExtension_smoothAt_normalization_pullback_of_dense_open_smooth`
quantifies over the witness universally instead, which is why it is the weaker form and why the
discharge happens here.

The fraction field is allowed its own universe, independent of the scheme's; the extension lives
in the scheme's universe, where the integral closure must live for its spectrum to be a scheme
there.  The passage is through `FractionRing A` and the `A`-algebra isomorphism any two fraction
rings admit, along which the extension's `K`-algebra structure is pulled back.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 032T](https://stacks.math.columbia.edu/tag/032T)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

/-- **The integral closure of `R` in `L` and the integral closure of `B` in `L` are the same
ring**, for a tower `R ⟶ B ⟶ L` with `B` integral over `R`: an element of `L` integral over `R`
is integral over `B`, and conversely an element integral over `B` is integral over `R` because
`B` is.  The isomorphism is the identity on elements of `L`, so it commutes with the two maps
from `R`.

The two closures are *equal* as subrings of `L`, by
`integralClosure_eq_restrictScalars_of_isIntegral`, but they are subalgebras over different
rings and hence different types; this is the ring isomorphism along which a statement about one
is carried to a statement about the other.  The tower hypothesis is taken as the equality of the
two ring maps `R ⟶ L` rather than as `IsScalarTower R B L`, so that a consumer with `B` a
subalgebra need not name the scalar action on `L` that the class quantifies over. -/
theorem exists_ringEquiv_integralClosure_of_isIntegral (R B L : Type u) [CommRing R] [CommRing B]
    [CommRing L] [Algebra R B] [Algebra B L] [Algebra R L] [Algebra.IsIntegral R B]
    (htower : algebraMap R L = (algebraMap B L).comp (algebraMap R B)) :
    ∃ ε : ↥(integralClosure R L) ≃+* ↥(integralClosure B L),
      (ε : ↥(integralClosure R L) →+* ↥(integralClosure B L)).comp
          (algebraMap R ↥(integralClosure R L)) =
        (algebraMap B ↥(integralClosure B L)).comp (algebraMap R B) := by
  have : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq' htower
  refine ⟨(Subalgebra.equivOfEq _ _
    (integralClosure_eq_restrictScalars_of_isIntegral R B L)).toRingEquiv, ?_⟩
  ext a
  change ((algebraMap R ↥(integralClosure R L)) a : L) = _
  simp [← IsScalarTower.algebraMap_apply R B L]

namespace AlgebraicGeometry

/-- **The two finite extensions of the reduced fibre theorem compose.**  Let `A` be a Nagata
Dedekind domain with fraction field `K`, let `f : X ⟶ Spec A` be flat, quasi-compact and locally
of finite type, let `L₀ / K` be finite with `B₀` the integral closure of `A` in `L₀`, and let `Y₀`
be the normalization of `X ×_{Spec A} Spec B₀`.  Let `L₁ / L₀` be finite and suppose the
normalization of `Y₀ ×_{Spec B₀} Spec B₁`, for `B₁` the integral closure of `B₀` in `L₁`, is
smooth over `Spec B₁` at every generic point of every fibre.  Then the normalization of
`X ×_{Spec A} Spec B`, for `B` the integral closure of `A` in `L₁`, is smooth over `Spec B` at
every generic point of every fibre.

Taking the normalized base change twice along the tower `A ⟶ B₀ ⟶ B₁` is taking it once
(`AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower`), smoothness and
the generic-point condition travel across the resulting isomorphism over `Spec B₁`, and `B₁` is
`B` up to the ring isomorphism `exists_ringEquiv_integralClosure_of_isIntegral`, along which the
conclusion is carried by `AlgebraicGeometry.smoothAt_normalization_pullback_of_isIso_base`. -/
theorem smoothAt_asFiber_genericPoints_normalization_pullback_of_tower
    {A : Type u} [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] (hA : IsNagataRing A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L₀ : Type u) [Field L₀] [Algebra K L₀] [FiniteDimensional K L₀] [Algebra A L₀]
    [IsScalarTower A K L₀] (L₁ : Type u) [Field L₁] [Algebra L₀ L₁] [FiniteDimensional L₀ L₁]
    [Algebra ↥(integralClosure A L₀) L₁] [Algebra A L₁] [IsScalarTower A L₀ L₁] [Algebra K L₁]
    [IsScalarTower K L₀ L₁] [IsScalarTower A K L₁]
    (htower₀ : algebraMap ↥(integralClosure A L₀) L₁ =
      (algebraMap L₀ L₁).comp (algebraMap ↥(integralClosure A L₀) L₀))
    (hsm : ∀ hW₀ : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ hV : ∀ V : (pullback ((pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).normalization hW₀ ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L₀)))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A L₀)
            ↥(integralClosure ↥(integralClosure A L₀) L₁)))) : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback ((pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).normalization hW₀ ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L₀)))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A L₀)
            ↥(integralClosure ↥(integralClosure A L₀) L₁)))) : Scheme.{u})) →
        (irreducibleComponents V).Finite,
      ∀ y : (pullback ((pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).normalization hW₀ ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L₀)))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A L₀)
            ↥(integralClosure ↥(integralClosure A L₀) L₁)))) : Scheme.{u}).normalizationScheme hV,
      (Scheme.normalization _ hV ≫ pullback.snd _ _).asFiber y ∈
        genericPoints ↥((Scheme.normalization _ hV ≫ pullback.snd _ _).fiber
          ((Scheme.normalization _ hV ≫ pullback.snd _ _).base y)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hV ≫ pullback.snd _ _) y) :
    ∀ hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L₁)))) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L₁)))) : Scheme.{u})) →
      (irreducibleComponents U).Finite,
    ∀ z : (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap A ↥(integralClosure A L₁)))) : Scheme.{u}).normalizationScheme hW,
    (Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L₁))))).asFiber z ∈
      genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map
        (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₁))))).fiber
          ((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
            (algebraMap A ↥(integralClosure A L₁))))).base z)) →
    InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₁))))) z := by
  have := IsScalarTower.of_algebraMap_eq' htower₀
  let : IsDedekindDomain ↥(integralClosure A L₀) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L₀ hA
  have : IsFractionRing ↥(integralClosure A L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension K L₀
  have hB₀ : IsNagataRing ↥(integralClosure A L₀) := isNagataRing_integralClosure K L₀ hA
  obtain ⟨hnorm₀, hflat₀, hlft₀, hqc₀⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K L₀ hA f
  have := hnorm₀
  have := hflat₀
  have := hlft₀
  have := hqc₀
  have : FiniteDimensional K L₁ := Module.Finite.trans L₀ L₁
  -- the two integral closures of `A` and of `B₀` in `L₁`, identified
  have htower : algebraMap A L₁ = (algebraMap ↥(integralClosure A L₀) L₁).comp
      (algebraMap A ↥(integralClosure A L₀)) := by
    rw [IsScalarTower.algebraMap_eq ↥(integralClosure A L₀) L₀ L₁, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A ↥(integralClosure A L₀) L₀,
      ← IsScalarTower.algebraMap_eq A L₀ L₁]
  have : IsDedekindDomain ↥(integralClosure ↥(integralClosure A L₀) L₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing L₀ L₁ hB₀
  have : IsDedekindDomain ↥(integralClosure A L₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L₁ hA
  have : UniversallyOpen (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(integralClosure A L₀) ↥(integralClosure ↥(integralClosure A L₀) L₁)))) :=
    universallyOpen_specMap_algebraMap_integralClosure L₀ L₁ hB₀
  obtain ⟨ε, hε⟩ :=
    exists_ringEquiv_integralClosure_of_isIntegral A ↥(integralClosure A L₀) L₁ htower
  have : IsIso (CommRingCat.ofHom (ε : ↥(integralClosure A L₁) →+*
      ↥(integralClosure ↥(integralClosure A L₀) L₁))) := (RingEquiv.toCommRingCatIso ε).isIso_hom
  intro hW
  -- the four morphisms of bases: `A ⟶ B₀ ⟶ B₁`, `A ⟶ B` and the identification `B ≅ B₁`
  set i₀ : Spec (.of ↥(integralClosure A L₀)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀))) with hi₀
  set hb : Spec (.of ↥(integralClosure ↥(integralClosure A L₀) L₁)) ⟶
      Spec (.of ↥(integralClosure A L₀)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A L₀)
      ↥(integralClosure ↥(integralClosure A L₀) L₁))) with hhb
  set i : Spec (.of ↥(integralClosure A L₁)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₁))) with hi
  set sb : Spec (.of ↥(integralClosure ↥(integralClosure A L₀) L₁)) ⟶
      Spec (.of ↥(integralClosure A L₁)) :=
    Spec.map (CommRingCat.ofHom (ε : ↥(integralClosure A L₁) →+*
      ↥(integralClosure ↥(integralClosure A L₀) L₁))) with hsb
  have hW₀ : ∀ U : (pullback f i₀ : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f i₀ : Scheme.{u})) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd f i₀)
  set r₀ : (pullback f i₀ : Scheme.{u}).normalizationScheme hW₀ ⟶
      Spec (.of ↥(integralClosure A L₀)) :=
    (pullback f i₀ : Scheme.{u}).normalization hW₀ ≫ pullback.snd f i₀ with hr₀
  have hV₁ : ∀ U : (pullback r₀ hb : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback r₀ hb : Scheme.{u})) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd r₀ hb)
  have hW₁ : ∀ U : (pullback f (hb ≫ i₀) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (hb ≫ i₀) : Scheme.{u})) →
      (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd f (hb ≫ i₀))
  -- taking the normalized base change twice along `A ⟶ B₀ ⟶ B₁` is taking it once
  obtain ⟨e, he⟩ :=
    exists_normalizationScheme_iso_normalization_pullback_tower hB₀ f i₀ hW₀ hV₁ hW₁
  obtain ⟨hnorm₂, hflat₂, hlft₂, hqc₂⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback L₀ L₁ hB₀ r₀
  have := hlft₂
  have : LocallyOfFinitePresentation ((pullback r₀ hb : Scheme.{u}).normalization hV₁ ≫
      pullback.snd r₀ hb) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  have : LocallyOfFinitePresentation ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
      pullback.snd f (hb ≫ i₀)) := by
    rw [← he]; infer_instance
  obtain ⟨hnorm₃, hflat₃, hlft₃, hqc₃⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K L₁ hA f
  have := hlft₃
  have : LocallyOfFinitePresentation ((pullback f i : Scheme.{u}).normalization hW ≫
      pullback.snd f i) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  -- across the tower comparison, an isomorphism over `Spec B₁`
  have he' : e.hom ≫ ((pullback r₀ hb : Scheme.{u}).normalization hV₁ ≫ pullback.snd r₀ hb) =
      ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫ pullback.snd f (hb ≫ i₀)) ≫
        (Iso.refl (Spec (.of ↥(integralClosure ↥(integralClosure A L₀) L₁)))).hom := by
    rw [Iso.refl_hom, Category.comp_id]
    exact he
  have H : ∀ y : (pullback f (hb ≫ i₀) : Scheme.{u}).normalizationScheme hW₁,
      ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
          pullback.snd f (hb ≫ i₀)).asFiber y ∈
        genericPoints ↥(((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
          pullback.snd f (hb ≫ i₀)).fiber
            (((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
              pullback.snd f (hb ≫ i₀)).base y)) →
      InfinitesimalLifting.SmoothAt ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
        pullback.snd f (hb ≫ i₀)) y := by
    intro y hy
    refine (InfinitesimalLifting.smoothAt_iso_hom_iff e (Iso.refl _) _ _ he' y).mpr
      (hsm hW₀ hV₁ (e.hom.base y) ?_)
    exact (mem_genericPoints_asFiber_iso_hom_iff e (Iso.refl _) _ _ he' y).mp hy
  -- across the isomorphism of the bases `integralClosure A L₁ ≅ integralClosure B₀ L₁`
  have hj : hb ≫ i₀ = sb ≫ i := by
    rw [hsb, hi, hi₀, hhb, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hε]
  exact smoothAt_normalization_pullback_of_isIso_base f i sb (hb ≫ i₀) hj hW₁ hW H


/-- **The reduced fibre theorem, for a fraction field in the scheme's own universe.**  Let `A` be
a Nagata Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat, quasi-compact
and locally of finite type.  Then there is a finite extension `L / K` such that, with `B` the
integral closure of `A` in `L`, the normalization of `X ×_{Spec A} Spec B` is smooth over
`Spec B` at every point which is a generic point of its own fibre.

The generic-point condition is stated in its ambient form, on a point of the normalization lying
over its own image; `AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_\
normalization_pullback` states it on the fibres themselves and allows `K` its own universe. -/
theorem exists_finiteExtension_smoothAt_asFiber_genericPoints_normalization_pullback
    {A : Type u} [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] (hA : IsNagataRing A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra A L) (_ : IsScalarTower A K L),
      ∀ hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ z : (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).normalizationScheme hW,
      (Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L))))).asFiber z ∈
        genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map
          (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))).fiber
            ((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L))))).base z)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))) z := by
  -- the first paragraph: the new base `B₀` and the new scheme `Y₀`
  obtain ⟨L₀, hL₀field, hL₀alg, hL₀fin, hAL₀, hAKL₀, hVex⟩ :=
    exists_finite_extension_dense_open_smooth_genericFibre_normalization K hA f
  let := hL₀field
  let := hL₀alg
  have := hL₀fin
  let := hAL₀
  have := hAKL₀
  let : IsDedekindDomain ↥(integralClosure A L₀) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L₀ hA
  have : IsFractionRing ↥(integralClosure A L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension K L₀
  have hB₀ : IsNagataRing ↥(integralClosure A L₀) := isNagataRing_integralClosure K L₀ hA
  obtain ⟨V, hVdense, hVsmooth⟩ := hVex
  obtain ⟨hnorm₀, hflat₀, hlft₀, hqc₀⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K L₀ hA f
  have := hnorm₀
  have := hflat₀
  have := hlft₀
  have := hqc₀
  -- the last paragraph, applied to the replacement
  obtain ⟨L₁, hL₁field, hL₁alg, hL₁fin, hB₀L₁, hB₀L₀L₁, hsm⟩ :=
    exists_finiteExtension_smoothAt_normalization_pullback_of_dense_open_smooth L₀ _ hB₀
      V hVdense hVsmooth
  let := hL₁field
  let := hL₁alg
  have := hL₁fin
  let := hB₀L₁
  have := hB₀L₀L₁
  -- the second extension read over `A` and over `K`
  let : Algebra A L₁ := ((algebraMap L₀ L₁).comp (algebraMap A L₀)).toAlgebra
  have : IsScalarTower A L₀ L₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra K L₁ := ((algebraMap L₀ L₁).comp (algebraMap K L₀)).toAlgebra
  have : IsScalarTower K L₀ L₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K L₁ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply K L₀ L₁, IsScalarTower.algebraMap_apply A L₀ L₁,
      ← IsScalarTower.algebraMap_apply A K L₀]
  have : FiniteDimensional K L₁ := Module.Finite.trans L₀ L₁
  exact ⟨L₁, hL₁field, inferInstance, inferInstance, inferInstance, inferInstance,
    smoothAt_asFiber_genericPoints_normalization_pullback_of_tower K hA f L₀ L₁
      (IsScalarTower.algebraMap_eq _ _ _) (fun _ ↦ hsm)⟩

/-- **Stacks Project, Tag 09IL (the reduced fibre theorem).**  Let `A` be a Nagata Dedekind
domain with fraction field `K` and let `f : X ⟶ Spec A` be flat, quasi-compact and locally of
finite type.  Then there is a finite extension `L / K` such that, with `B` the integral closure
of `A` in `L`, the normalization `Y` of `X ×_{Spec A} Spec B` is smooth over `Spec B` at every
generic point of every one of the fibres of `Y ⟶ Spec B`.

`X` is assumed neither reduced nor normal nor affine, and `A` is not assumed excellent; the
smoothness is at *all* generic points of *all* fibres.

The fraction field is allowed its own universe: the statement is the one in the scheme's universe
transported along the `A`-algebra isomorphism `K ≃ₐ[A] FractionRing A`, which carries the
`K`-algebra structure of the extension and its finite dimensionality while leaving the extension,
the integral closure and the whole conclusion where they are. -/
@[stacks 09IL]
theorem exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback
    {A : Type u} [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K]
    [Algebra A K] [IsFractionRing A K] (hA : IsNagataRing A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra A L) (_ : IsScalarTower A K L),
      ∃ hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ b : Spec (.of ↥(integralClosure A L)),
      ∀ y : (Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L))))).fiber b,
      y ∈ genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map
        (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))).fiber b) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L)))))
        ((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L))))).fiberι b y) := by
  obtain ⟨L, hLfield, hFL, hFLfin, hAL, hAFL, hconc⟩ :=
    exists_finiteExtension_smoothAt_asFiber_genericPoints_normalization_pullback
      (FractionRing A) hA f
  let := hLfield
  let := hFL
  have := hFLfin
  let := hAL
  have := hAFL
  -- the two fraction fields of `A`, identified
  let e : K ≃ₐ[A] FractionRing A :=
    IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)
  let : Algebra K (FractionRing A) := (e : K →+* FractionRing A).toAlgebra
  let : Algebra K L := ((algebraMap (FractionRing A) L).comp (e : K →+* FractionRing A)).toAlgebra
  have : IsScalarTower K (FractionRing A) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite K (FractionRing A) :=
    Module.Finite.of_surjective (Algebra.linearMap K (FractionRing A)) fun x ↦
      ⟨e.symm x, e.apply_symm_apply x⟩
  have : FiniteDimensional K L := Module.Finite.trans (FractionRing A) L
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    have h1 : algebraMap K L (algebraMap A K a)
        = algebraMap (FractionRing A) L (e (algebraMap A K a)) := rfl
    rw [h1, e.commutes a, ← IsScalarTower.algebraMap_apply A (FractionRing A) L]
  -- The integral closure of `A` in `L` is Dedekind, hence Noetherian, so the base change has
  -- finitely many irreducible components over every quasi-compact open: the finiteness witness
  -- the normalization needs is a theorem, not a hypothesis.
  have : IsDedekindDomain (integralClosure A L) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L hA
  refine ⟨L, hLfield, inferInstance, inferInstance, hAL, inferInstance,
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))),
    fun b y hy ↦ ?_⟩
  exact hconc _ _ (mem_genericPoints_asFiber_fiberι _ b y hy)

end AlgebraicGeometry

end
