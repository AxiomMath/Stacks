module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumHomEquiv
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Properness
import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Rig-surjectivity of the completion of a proper morphism

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`, with `U ⊂ X` the open
subspace with `|U| = |X| ∖ T` and `U' = f⁻¹U ⊂ X'`; this is the situation of **Stacks 0GDB**.
Here `U` is `AlgebraicGeometry.Space.openSubspaceOfPoints` on `Tᶜ`, whose point set is `Tᶜ` by
Stacks 03BZ, `U' = f⁻¹U` is its preimage subfunctor — by
`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints` the open subspace of `X'` cut out by
`(|f|⁻¹T)ᶜ` — and the restriction `U' ⟶ U` is `CategoryTheory.Subfunctor.fromPreimage`.

**Stacks 0AQW** says that if `T` is closed, `f` is proper and `U' → U` is surjective, then the
morphism of completions `f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-surjective.

The proof has two steps. The valuative step: let `R` be a discrete valuation ring whose
spectrum lies in the site, let `Spec R ⟶ S` be a structure morphism and let `g : Spec R ⟶ X`
be a point of `X` over it whose generic point does not lie over `T`. Then there are an
extension `R ⊂ R'` of discrete valuation rings with `R'` complete and a point `Spec R' ⟶ X'`
of `X'` lying over `g`. Surjectivity of `U' → U` produces a point of `X'` over the generic point
of `Spec R`, the residue field `L` of a point of `Spec K ×_X X'` is essentially of finite type
over the fraction field `K` of `R` because `f` is locally of finite type, **Stacks 00PH**
produces inside `L` a discrete valuation ring `A` dominating `R`, the valuative criterion of
properness **Stacks 0A40** lifts the resulting square to `X'`, and **Stacks 0AP1** makes the
`𝔪_A`-adic completion of `A` a discrete valuation ring again, this time complete.

The formal step: an adic morphism `Spf R ⟶ X_{/T}` out of a complete discrete valuation ring
algebraizes by **Stacks 0GBU** to a point `Spec R ⟶ X` whose fibre over `T` is the closed
point, so its generic point lies outside `T` and the valuative step applies. The resulting
point `Spec R' ⟶ X'`, restricted to `Spf R'`, lands in `X'_{/T'}` because the completion square
of **Stacks 0APV** is cartesian.

## Main definitions

* `AlgebraicGeometry.Space.specSiteObjectMap`: the morphism of site objects over `S` induced
  by a homomorphism of rings whose spectra lie in the site.
* `AlgebraicGeometry.Space.genericFieldValuedPoint`: the generic point of `Spec R`, for `R` a
  domain, read as a field-valued point of a presheaf through an `R`-point of it.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_completionSheafMap`: **Stacks 0AQW**.
* `AlgebraicGeometry.Space.exists_isExtension_lift_of_isProper_of_isSurjective`: the valuative
  step of the proof of Stacks 0AQW.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_comp_formalSpectrumToSpec`: the canonical
  maps `Spf ⟶ Spec` are natural in a continuous homomorphism over `S`.
* `AlgebraicGeometry.Space.mem_range_pointsMap_of_notMem_of_isSurjective`: a point of `X`
  outside `T` is in the image of `|X'|` once `U' → U` is surjective.
* `AlgebraicGeometry.Space.exists_essFiniteType_fieldValuedPoint`: an algebraic space with a
  point, locally of finite type over the spectrum of a field `K`, has a field-valued point
  whose field is essentially of finite type over `K`.

## Implementation notes

The hypothesis that `X` be locally Noetherian, which **Stacks 0AQW** also carries, is not
needed. In the source it makes `X_{/T}` and `X'_{/T'}` locally Noetherian formal algebraic
spaces, so that rig-surjectivity is defined for `f_{/T}`, and it gives the quasi-compactness
of `U ⟶ X` in the statement of **Stacks 0GBU**. The proof of 0GBU does not use that
quasi-compactness, so the existence of the algebraization and the inclusion `g⁻¹(T) ⊆ {𝔪}`
are applied directly, as `AlgebraicGeometry.FormalSpace.surjective_map_into_algebraicSpace`
and `AlgebraicGeometry.FormalSpace.preimageSubsetClosedPoint_of_comp_eq`.

The lift `Spf R' ⟶ X'_{/T'}` is the morphism into the fibre product
`X'_{/T'} = X' ×_X X_{/T}` of Stacks 0APV whose components are the restriction of
`Spec R' ⟶ X'` to `Spf R'` and the composite `Spf R' ⟶ Spf R ⟶ X_{/T}`. Their agreement in `X`
is checked by Yoneda's lemma for sheaves of sets: both are the restriction to `Spf R'` of
`Spec R' ⟶ Spec R ⟶ X`, by naturality of `Spf ⟶ Spec`. The quotient system on `R'` is the
one of its ordinary spectrum, `AlgebraicGeometry.FormalSpace.quotientSystemOfSpec`, over `S`
through `Spec R' ⟶ Spec R ⟶ S`.

The point of `X'` over the generic point of `Spec R` is used only to see that the fibre product
`Spec K ×_X X'` has a point at all; the field-valued point of that fibre product whose residue
field is taken need not be the given one, and
`AlgebraicGeometry.Space.exists_essFiniteType_fieldValuedPoint` therefore takes a point of the
space merely as a nonemptiness witness. Its proof reads the residue field off an étale scheme
chart, where being essentially of finite type over `K` is
`AlgebraicGeometry.essFiniteType_preimage_residueField`.

The extension `R ⊂ R'` is recorded as `IsDiscreteValuationRing.IsExtension` of Stacks 09E4, an
injective local algebra map, and the completeness of `R'` as `IsAdicComplete` for its maximal
ideal, together with the maximal-adic topology; this is the shape in which
`AlgebraicGeometry.FormalSpace.IsRigSurjective` asks for the extension it produces.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0A40](https://stacks.math.columbia.edu/tag/0A40)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
* [Stacks Project, Tag 0AQW](https://stacks.math.columbia.edu/tag/0AQW)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0GBU](https://stacks.math.columbia.edu/tag/0GBU)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The adic completion of a ring injects into the product of its quotient stages, so its
cardinality is bounded by that of a countable product of copies of the ring. -/
theorem mk_adicCompletion_le (R : Type u) [CommRing R] (I : Ideal R) :
    Cardinal.mk (AdicCompletion I R) ≤
      (max Cardinal.aleph0 (Cardinal.mk R)) ^ Cardinal.aleph0 := by
  classical
  let rep (n : ℕ) : (R ⧸ (I ^ n • (⊤ : Submodule R R))) → R := fun x =>
    Classical.choose (Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R R)) x)
  have hrep (n : ℕ) (x : R ⧸ (I ^ n • (⊤ : Submodule R R))) :
      Submodule.mkQ (I ^ n • (⊤ : Submodule R R)) (rep n x) = x :=
    Classical.choose_spec (Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R R)) x)
  have hinj : Function.Injective (fun x : AdicCompletion I R => fun n => rep n (x.val n)) := by
    intro x y h
    apply Subtype.ext
    funext n
    calc
      x.val n = Submodule.mkQ (I ^ n • (⊤ : Submodule R R)) (rep n (x.val n)) :=
        (hrep n (x.val n)).symm
      _ = Submodule.mkQ (I ^ n • (⊤ : Submodule R R)) (rep n (y.val n)) :=
        congrArg _ (congrFun h n)
      _ = y.val n := hrep n (y.val n)
  calc
    Cardinal.mk (AdicCompletion I R) ≤ Cardinal.mk (ℕ → R) := Cardinal.mk_le_of_injective hinj
    _ ≤ (max Cardinal.aleph0 (Cardinal.mk R)) ^ Cardinal.aleph0 := by
      rw [Cardinal.mk_pi, Cardinal.prod_const]
      simpa [Cardinal.mk_nat] using
        Cardinal.power_le_power_right (le_max_right Cardinal.aleph0 (Cardinal.mk R))

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Site objects attached to ring homomorphisms -/

/-- The spectrum of the fraction field of a domain whose spectrum lies in the big site again
lies in the big site, by Stacks 000R (9)(c). -/
theorem contains_spec_fractionRing {R : Type u} [CommRing R] [IsDomain R]
    (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of (FractionRing R))) :=
  Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (nonZeroDivisors R) (FractionRing R) hR

/-- The morphism of site objects over `S` induced by a homomorphism `φ : R →+* C` of rings
whose spectra lie in the big site: the spectrum of `C` is taken over `S` through `φ` and the
given structure morphism of the spectrum of `R`. -/
def specSiteObjectMap {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
    (hR : B.Contains (Spec (.of R))) (hC : B.Contains (Spec (.of C)))
    (a : Spec (.of R) ⟶ S) :
    siteObject B S hS hC (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ siteObject B S hS hR a :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ)))

/-- The generic point of the spectrum of a domain `R` whose spectrum lies in the big site,
read as a field-valued point of a presheaf `X` through an `R`-point of `X`: its field is the
fraction field of `R` and its section is the restriction of the given one. -/
def genericFieldValuedPoint {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R : Type u} [CommRing R]
    [IsDomain R] (hR : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (s : X.obj (op (siteObject B S hS hR a))) : FieldValuedPoint B S hS X where
  carrier := FractionRing R
  contained := contains_spec_fractionRing hR
  toBase := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ a
  value := X.map (specSiteObjectMap (algebraMap R (FractionRing R)) hR
    (contains_spec_fractionRing hR) a).op s

/-! ### A point outside `T` comes from the source -/

/-- If the restriction `U' ⟶ U` to the open complements of `T` and of its inverse image is
surjective, then every point of `X` outside `T` is the image of a point of `X'`: the point
lies in the image of `|U|`, hence in the image of `|U'|`, and the restriction to the open
complements is the restriction of `f`. -/
theorem mem_range_pointsMap_of_notMem_of_isSurjective
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) (T : Set (points B S hS X))
    (hsurj : IsSurjective B S hS ((openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f))
    {x : points B S hS X} (hx : x ∉ T) :
    x ∈ Set.range (pointsMap B S hS X' f) := by
  obtain ⟨z, hz⟩ : x ∈ Set.range (pointsMap B S hS
      (openSubspaceOfPoints B S hS X Tᶜ).toFunctor (openSubspaceOfPoints B S hS X Tᶜ).ι) := by
    rwa [range_pointsMap_ι_openSubspaceOfPoints]
  obtain ⟨z', hz'⟩ := hsurj z
  refine ⟨pointsMap B S hS _ ((openSubspaceOfPoints B S hS X Tᶜ).preimage f).ι z', ?_⟩
  have key : pointsMap B S hS X' f
        (pointsMap B S hS _ ((openSubspaceOfPoints B S hS X Tᶜ).preimage f).ι z') =
      pointsMap B S hS _ (openSubspaceOfPoints B S hS X Tᶜ).ι
        (pointsMap B S hS _ ((openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f) z') := by
    rw [← Function.comp_apply (f := pointsMap B S hS X' f), ← pointsMap_comp,
      ← Function.comp_apply
        (f := pointsMap B S hS _ (openSubspaceOfPoints B S hS X Tᶜ).ι), ← pointsMap_comp]
    rfl
  rw [key, hz', hz]

/-! ### A field-valued point with residue field essentially of finite type -/

/-- An algebraic space over `S` with a point, locally of finite type over the spectrum of a
field `K` lying in the site, has a field-valued point whose field is essentially of finite type
over `K`.

The point is lifted to an étale scheme chart `V` of the space, and the field-valued point is
the residue field of the corresponding point of `V`, whose spectrum lies in the site because
the morphism from it to `V` is a quasi-compact monomorphism. That the residue field is
essentially of finite type over `K` is
`AlgebraicGeometry.essFiniteType_preimage_residueField`, the chart `V` being locally of finite
type over `Spec K`. -/
theorem exists_essFiniteType_fieldValuedPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S)
    (π : F ⟶ yoneda.obj (siteObject B S hS hK b)) (hπ : IsLocallyOfFiniteType B S hS π)
    (z : points B S hS F) :
    ∃ q : FieldValuedPoint B S hS F,
      (Spec.preimage (B.inclusion.map
        (π.app (op (q.siteObject B S hS F)) q.value).left)).hom.EssFiniteType := by
  classical
  let k := siteObject B S hS hK b
  obtain ⟨V, t, htS, htE⟩ := hF.exists_atlas
  obtain ⟨vcls, hvcls⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF V t).mp htS z
  obtain ⟨vpt, hvpt⟩ := Quot.exists_rep vcls
  let Vsch := (BigFppfOver.toScheme B S hS).obj V
  let v : Vsch := schemePoint B S hS V vpt
  let bV : V ⟶ k := yoneda.preimage (t ≫ π)
  have hb : yoneda.map bV = t ≫ π := yoneda.map_preimage _
  have := isMultiplicative_presheaf_etale B S hS
  have hid : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj k)) :=
    MorphismProperty.id_mem _ _
  have hVft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map bV) :=
    hπ V k t (𝟙 _) bV htE hid (by simpa using hb)
  have : QuasiCompact (Vsch.fromSpecResidueField v) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    exact fun W _ => (Set.toFinite (Vsch.fromSpecResidueField v ⁻¹' (W : Set Vsch))).isCompact
  have hL : B.Contains (Spec (Vsch.residueField v)) :=
    (Scheme.size_le_of_mono_quasiCompact (Vsch.fromSpecResidueField v)).trans_lt
      V.left.property
  let aL := Vsch.fromSpecResidueField v ≫ B.inclusion.map V.hom
  let l := siteObject B S hS hL aL
  let j : l ⟶ V := Over.homMk (ObjectProperty.homMk (Vsch.fromSpecResidueField v))
  let q : FieldValuedPoint B S hS F := ⟨Vsch.residueField v, hL, aL, t.app (op l) j⟩
  refine ⟨q, ?_⟩
  have hval : π.app (op (q.siteObject B S hS F)) q.value = j ≫ bV := by
    show (t ≫ π).app (op l) j = _
    rw [← hb]
    rfl
  rw [hval]
  exact essFiniteType_preimage_residueField K
    ((BigFppfOver.toScheme B S hS).map bV) v

/-! ### The valuative step of the proof of Stacks 0AQW -/

/-- The morphism of site objects over `S` given by a morphism `u` of the underlying schemes. -/
private def siteObjectHomMk {Y Z : Scheme.{u}} (hY : B.Contains Y) (hZ : B.Contains Z)
    {a : Y ⟶ S} {b : Z ⟶ S} (u : Y ⟶ Z) (h : u ≫ b = a) :
    siteObject B S hS hY a ⟶ siteObject B S hS hZ b :=
  Over.homMk (ObjectProperty.homMk u) (by apply ObjectProperty.hom_ext; exact h)

/-- The completion step of the proof of Stacks 0AQW: a point of `X'` over an `R`-point of `X`
defined on a discrete valuation ring `A` dominating `R` extends, by Stacks 0AP1, to the
`𝔪_A`-adic completion of `A`, a complete discrete valuation ring extending `R`. -/
private theorem exists_isExtension_lift_of_lift_adicCompletion
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (s : X.obj (op (siteObject B S hS hR a)))
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)] (hinjRA : Function.Injective (algebraMap R A))
    (hAsite : B.Contains (Spec (.of A)))
    (z : yoneda.obj (siteObject B S hS hAsite
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a)) ⟶ X')
    (hz : z ≫ f = yoneda.map (specSiteObjectMap (algebraMap R A) hR hAsite a) ≫
      yonedaEquiv.symm s) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra R C) (_ : IsDiscreteValuationRing.IsExtension R C)
      (_ : TopologicalSpace C) (_ : IsTopologicalRing C) (_ : IsLinearTopology C C),
      IsAdic (IsLocalRing.maximalIdeal C) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧
          ∃ (hC : B.Contains (Spec (.of C)))
            (y : yoneda.obj (siteObject B S hS hC
              (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ a)) ⟶ X'),
            y ≫ f = yoneda.map (specSiteObjectMap (algebraMap R C) hR hC a) ≫
              yonedaEquiv.symm s := by
  let aA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a
  let aToR : siteObject B S hS hAsite aA ⟶ siteObject B S hS hR a :=
    specSiteObjectMap (algebraMap R A) hR hAsite a
  -- the completion of `A`, a complete discrete valuation ring extending `R`, by Stacks 0AP1
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  obtain ⟨hCdomain, hCdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := A)).mp
      ⟨inferInstance, inferInstance⟩
  let : IsDomain C := hCdomain
  let : IsDiscreteValuationRing C := hCdvr
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  have hinjRC : Function.Injective (algebraMap R C) :=
    (AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A).comp hinjRA
  let : IsDiscreteValuationRing.IsExtension R C :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective R C).mpr hinjRC
      toIsLocalHom := (algebraMap A C).isLocalHom_comp (algebraMap R A) }
  let : TopologicalSpace C := (IsLocalRing.maximalIdeal C).adicTopology
  let : IsTopologicalRing C := inferInstance
  let : IsLinearTopology C C := (IsLocalRing.maximalIdeal C).isLinearTopology
  have hCsite : B.Contains (Spec (.of C)) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of C) hAsite
      (by
        simpa only [Scheme.size_Spec] using
          mk_adicCompletion_le A (IsLocalRing.maximalIdeal A))
  let cToA : siteObject B S hS hCsite
      (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ a) ⟶ siteObject B S hS hAsite aA :=
    siteObjectHomMk hCsite hAsite (Spec.map (CommRingCat.ofHom (algebraMap A C))) (by
      dsimp only [aA]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hcomp : cToA ≫ aToR = specSiteObjectMap (algebraMap R C) hR hCsite a := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, rfl, inferInstance, hCsite,
    yoneda.map cToA ≫ z, ?_⟩
  rw [Category.assoc, hz]
  show yoneda.map cToA ≫ yoneda.map aToR ≫ yonedaEquiv.symm s = _
  rw [← Category.assoc, ← Functor.map_comp, hcomp]

/-- The fibre-product step of the proof of Stacks 0AQW. If `U' ⟶ U` is surjective and `f` is
locally of finite type, then the fibre product of `f` with the generic point of an `R`-point of
`X` outside `T` has a field-valued point whose field is essentially of finite type over the
fraction field `K` of `R`.

Surjectivity of `U' ⟶ U` produces a point of `X'` over the generic point, hence a point of the
fibre product, which is locally of finite type over `Spec K` by base change; the field-valued
point is `AlgebraicGeometry.Space.exists_essFiniteType_fieldValuedPoint`. -/
private theorem exists_essFiniteType_fieldValuedPoint_pullback
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (points B S hS X)) (hf : IsLocallyOfFiniteType B S hS f)
    (hsurj : IsSurjective B S hS ((openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f))
    (R : Type u) [CommRing R] [IsDomain R]
    (hR : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (s : X.obj (op (siteObject B S hS hR a)))
    (hgen : (genericFieldValuedPoint hR a s).class B S hS X ∉ T) :
    ∃ l : FieldValuedPoint B S hS
        (pullback (yonedaEquiv.symm (genericFieldValuedPoint hR a s).value) f),
      (Spec.preimage (B.inclusion.map
        ((pullback.fst (yonedaEquiv.symm (genericFieldValuedPoint hR a s).value) f).app
          (op (l.siteObject B S hS _)) l.value).left)).hom.EssFiniteType := by
  classical
  -- the generic point of `Spec R` as a point of `X`, and a point of `X'` above it
  let p : FieldValuedPoint B S hS X := genericFieldValuedPoint hR a s
  obtain ⟨r, i, hi⟩ := exists_fieldValuedPoint_of_class_mem_range f p
    (mem_range_pointsMap_of_notMem_of_isSurjective f T hsurj hgen)
  -- the fibre product of the generic point with `f`, which therefore has a point
  let ξ : yoneda.obj (p.siteObject B S hS X) ⟶ X := yonedaEquiv.symm p.value
  let P := pullback ξ f
  have hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS _) hX' hX
  let j : yoneda.obj (r.siteObject B S hS X') ⟶ P :=
    pullback.lift (yoneda.map i) (yonedaEquiv.symm r.value) (by
      dsimp only [ξ]
      rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_right]
      exact congrArg yonedaEquiv.symm hi.symm)
  let pt : FieldValuedPoint B S hS P := ⟨r.carrier, r.contained, r.toBase, yonedaEquiv j⟩
  have hπ : IsLocallyOfFiniteType B S hS (pullback.fst ξ f) :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk ξ : (⟨yoneda.obj (p.siteObject B S hS X),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
        (ObjectProperty.homMk f : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)).flip hf
  exact exists_essFiniteType_fieldValuedPoint hP (FractionRing R) (contains_spec_fractionRing hR)
    p.toBase (pullback.fst ξ f) hπ (pt.class B S hS P)

/-- The valuative step of the proof of Stacks 0AQW for a field-valued point. Let `f` be proper,
let `R` be a discrete valuation ring whose spectrum lies in the big site with an `R`-point `s` of
`X`, and let `L` be a field essentially of finite type over the fraction field `K` of `R` with an
`L`-point of `X'` over `s`. Then there is an extension `R ⊂ R'` of discrete valuation rings with
`R'` complete for its maximal-adic topology, whose spectrum lies in the big site, together with
an `R'`-point of `X'` lying over `s`.

Stacks 00PH produces inside `L` a discrete valuation ring `A` with fraction field `L`
dominating `R`; the `L`-point and the `R`-point form a valuative square for `f`, which the
valuative criterion of properness, Stacks 0A40, solves, and the lift is extended to the
completion of `A` by `AlgebraicGeometry.Space.exists_isExtension_lift_of_lift_adicCompletion`. -/
private theorem exists_isExtension_lift_of_isProper_of_essFiniteType
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : IsProper B S hS f)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (s : X.obj (op (siteObject B S hS hR a)))
    (L : Type u) [Field L] [Algebra (FractionRing R) L] [Algebra.EssFiniteType (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L] (hL : B.Contains (Spec (.of L)))
    (g : yoneda.obj (siteObject B S hS hL (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ a)) ⟶
      X')
    (hg : g ≫ f = yoneda.map (specSiteObjectMap (algebraMap R L) hR hL a) ≫
      yonedaEquiv.symm s) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra R C) (_ : IsDiscreteValuationRing.IsExtension R C)
      (_ : TopologicalSpace C) (_ : IsTopologicalRing C) (_ : IsLinearTopology C C),
      IsAdic (IsLocalRing.maximalIdeal C) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧
          ∃ (hC : B.Contains (Spec (.of C)))
            (y : yoneda.obj (siteObject B S hS hC
              (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ a)) ⟶ X'),
            y ≫ f = yoneda.map (specSiteObjectMap (algebraMap R C) hR hC a) ≫
              yonedaEquiv.symm s := by
  -- a discrete valuation ring inside `L` dominating `R`, by Stacks 00PH
  obtain ⟨A, _, _, _⟩ :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField (FractionRing R)
      (L := L) (IsDiscreteValuationRing.not_isField R)
  have hAsite : B.Contains (Spec (.of A)) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A.toSubring hL
  have hRL : algebraMap R L = (algebraMap A L).comp (algebraMap R A) :=
    IsScalarTower.algebraMap_eq R A L
  let aA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ aA =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ a := by
    dsimp only [aA]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hRL]
  -- the valuative square and its solution, by Stacks 0A40
  let lid := siteObjectHomMk (hS := hS) hL hL (𝟙 (Spec (.of L)))
    ((Category.id_comp _).trans hbase.symm)
  let γ := specSiteObjectMap (hS := hS) (algebraMap A L) hAsite hL aA
  have hd : lid ≫ specSiteObjectMap (algebraMap R L) hR hL a =
      γ ≫ specSiteObjectMap (algebraMap R A) hR hAsite a := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hRL]
  let sq : ValuativeSquare f :=
    { R := A, K := L, ring_mem := hAsite, field_mem := hL, base := aA
      generic := yoneda.map lid ≫ g
      special := yoneda.map (specSiteObjectMap (algebraMap R A) hR hAsite a) ≫
        yonedaEquiv.symm s
      comm := by
        rw [Category.assoc, hg, ← Functor.map_comp_assoc, hd]
        exact Functor.map_comp_assoc _ _ _ _ }
  obtain ⟨lift⟩ :=
    ((isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated hX' hX f hf.2.1
      (isQuasiSeparated_of_isSeparated B S hS hf.1)).mp hf sq).1
  have hinjRA : Function.Injective (algebraMap R A) := by
    apply Function.Injective.of_comp (f := algebraMap A L)
    rw [← RingHom.coe_comp, ← hRL, IsScalarTower.algebraMap_eq R (FractionRing R) L,
      RingHom.coe_comp]
    exact (algebraMap (FractionRing R) L).injective.comp
      (IsFractionRing.injective R (FractionRing R))
  exact exists_isExtension_lift_of_lift_adicCompletion f R hR a s A hinjRA hAsite lift.map
    lift.special_comm

/-- The valuative step of the proof of Stacks 0AQW. In the situation of Stacks 0GDB, let `f`
be proper and let the restriction `U' ⟶ U` to the open complements be surjective. Let `R` be a
discrete valuation ring whose spectrum lies in the big site, let `a : Spec R ⟶ S` be a
structure morphism and let `s` be an `R`-point of `X` over `a` whose generic point does not lie
over `T`. Then there is an extension `R ⊂ R'` of discrete valuation rings with `R'` complete
for its maximal-adic topology, whose spectrum lies in the big site, together with an
`R'`-point of `X'` lying over `s`.

Surjectivity of `U' ⟶ U` produces a point of `X'` over the generic point of `Spec R`, so the
fibre product `Spec K ×_X X'` of the generic point with `f` has a point, `K` being the fraction
field of `R`. That fibre product is locally of finite type over `Spec K`, `f` being so, hence
has a field-valued point whose field `L` is essentially of finite type over `K`; Stacks 00PH
produces inside `L` a discrete valuation ring `A` with fraction field `L` dominating `R`, and
the generic point of `Spec A` together with the given `R`-point form a valuative square for
`f`, which the valuative criterion of properness, Stacks 0A40, solves. Finally the
`𝔪_A`-adic completion of `A` is again a discrete valuation ring by Stacks 0AP1, is complete,
and extends `R`; the lift is restricted along it. -/
theorem exists_isExtension_lift_of_isProper_of_isSurjective
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (points B S hS X)) (hf : IsProper B S hS f)
    (hsurj : IsSurjective B S hS ((openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f))
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : B.Contains (Spec (.of R))) (a : Spec (.of R) ⟶ S)
    (s : X.obj (op (siteObject B S hS hR a)))
    (hgen : (genericFieldValuedPoint hR a s).class B S hS X ∉ T) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra R C) (_ : IsDiscreteValuationRing.IsExtension R C)
      (_ : TopologicalSpace C) (_ : IsTopologicalRing C) (_ : IsLinearTopology C C),
      IsAdic (IsLocalRing.maximalIdeal C) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧
          ∃ (hC : B.Contains (Spec (.of C)))
            (y : yoneda.obj (siteObject B S hS hC
              (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ a)) ⟶ X'),
            y ≫ f = yoneda.map (specSiteObjectMap (algebraMap R C) hR hC a) ≫
              yonedaEquiv.symm s := by
  obtain ⟨l, hl⟩ := exists_essFiniteType_fieldValuedPoint_pullback hX' hX f T hf.2.1.1 hsurj R hR
    a s hgen
  let K := FractionRing R
  have hK : B.Contains (Spec (.of K)) := contains_spec_fractionRing hR
  let p : FieldValuedPoint B S hS X := genericFieldValuedPoint hR a s
  let ξ : yoneda.obj (p.siteObject B S hS X) ⟶ X := yonedaEquiv.symm p.value
  have hξ : ξ = yoneda.map (specSiteObjectMap (algebraMap R K) hR hK a) ≫ yonedaEquiv.symm s :=
    yonedaEquiv_symm_map _ s
  -- the field `L` of that point, essentially of finite type over `K`
  let L := l.carrier
  let lK : l.siteObject B S hS _ ⟶ p.siteObject B S hS X :=
    (pullback.fst ξ f).app (op (l.siteObject B S hS _)) l.value
  let φ : K →+* L := (Spec.preimage (B.inclusion.map lK.left)).hom
  let : Algebra K L := φ.toAlgebra
  let : Algebra.EssFiniteType K L := hl
  let : Algebra R L := (φ.comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  have hφ : Spec.map (CommRingCat.ofHom φ) = B.inclusion.map lK.left := Spec.map_preimage _
  have hbaseL : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ a = l.toBase := by
    rw [show algebraMap R L = φ.comp (algebraMap R K) from rfl, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hφ]
    exact congrArg B.inclusion.map lK.w
  let lid : siteObject B S hS l.contained (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ a) ⟶
      l.siteObject B S hS _ :=
    siteObjectHomMk _ _ (𝟙 (Spec (.of L))) ((Category.id_comp _).trans hbaseL.symm)
  have hd : lid ≫ lK ≫ specSiteObjectMap (algebraMap R K) hR hK a =
      specSiteObjectMap (algebraMap R L) hR l.contained a := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show 𝟙 _ ≫ (B.inclusion.map lK.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      Spec.map (CommRingCat.ofHom (algebraMap R L))
    rw [show algebraMap R L = φ.comp (algebraMap R K) from rfl, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.id_comp, hφ]
    rfl
  have hlK : yonedaEquiv.symm l.value ≫ pullback.fst ξ f = yoneda.map lK := by
    rw [yonedaEquiv_symm_naturality_right]
    exact (yonedaEquiv.symm_apply_eq).mpr (yonedaEquiv_yoneda_map lK).symm
  refine exists_isExtension_lift_of_isProper_of_essFiniteType hX' hX f hf R hR a s L l.contained
    (yoneda.map lid ≫ yonedaEquiv.symm l.value ≫ pullback.snd ξ f) ?_
  rw [Category.assoc, Category.assoc, ← pullback.condition,
    ← Category.assoc (yonedaEquiv.symm l.value), hlK, hξ]
  have h2 := congrArg (fun u => yoneda.map u ≫ yonedaEquiv.symm s) hd
  simp only [Functor.map_comp, Category.assoc] at h2
  exact h2

end Space

namespace FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Rig-surjectivity of a completed proper morphism -/

/-- The inclusion `X_{/T} ⟶ X` into the sheafified universe lift of an algebraic space is the
inclusion into its universe lift followed by the identification of the universe lift with its
sheafification. -/
theorem completionSheafInclusion_eq_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) :
    Space.completionSheafInclusion B S hS X T =
      completionToUpliftedSheaf X hX T ≫
        ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X hX.isSheaf).hom := by
  apply ObjectProperty.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _
    (Space.sheafifiedULift B S hS X).property
  show (BigFppfOver.topology B S hS).toSheafify _ ≫
      (BigFppfOver.topology B S hS).sheafifyMap (Space.completionSubfunctor B S hS X T).ι =
    (BigFppfOver.topology B S hS).toSheafify _ ≫
      (Space.completionSheafToAmbient B S hS X _ T ≫
        (BigFppfOver.topology B S hS).toSheafify _)
  rw [← (BigFppfOver.topology B S hS).toSheafify_naturality]
  exact (congrArg (· ≫ (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}))
    (Space.toSheafify_comp_completionSheafToAmbient B S hS X _ T)).symm.trans
      (Category.assoc _ _ _)

/-- The formal spectrum of the target of a continuous homomorphism of rings over `S` maps to the
ordinary spectrum of the source in two ways which agree: through the formal spectrum of the
source, or through the ordinary spectrum of the target. Both are checked on each quotient stage
of the target, where they are the spectrum of one ring map. -/
theorem formalSpectrumMap_comp_formalSpectrumToSpec {R C : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] [CommRing C]
    [TopologicalSpace C] {I : Ideal R} {I' : Ideal C} (hI : IsAdic I) (hI' : IsAdic I')
    (hR : TopologicalRing.IsWeaklyAdmissible R) {D : QuotientSystem B S hS R}
    {D' : QuotientSystem B S hS C} (e : ContinuousHom D D') (hIe : I.map e.toRingHom ≤ I')
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hCS : B.Contains (Spec (.of C)))
    (hq' : ∀ K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
          (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q) = D'.overS K) :
    formalSpectrumMap hR e ≫ formalSpectrumToSpec D hRS q hq =
      formalSpectrumToSpec D' hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q) hq' ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (X := (BigAffineFppf.inclusion B S hS).obj
            (specOver hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)))
          (Y := (BigAffineFppf.inclusion B S hS).obj (specOver hRS q))
          (Space.specSiteObjectMap e.toRingHom hRS hCS q) := by
  refine formalSpectrum_hom_ext D' _ fun K' => ?_
  obtain ⟨n, hn⟩ := exists_pow_le_of_isWeakIdealOfDefinition hI' K'
  let J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hI (Nat.succ_ne_zero n)⟩
  have hJ : J.1 ≤ Ideal.comap e.toRingHom K'.1 := by
    refine Ideal.map_le_iff_le_comap.mp (le_trans ?_ hn)
    rw [Ideal.map_pow]
    exact (pow_le_pow_left' hIe (n + 1)).trans (Ideal.pow_le_pow_right (Nat.le_succ n))
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let ι := BigAffineFppf.inclusion B S hS
  have hstage : ι.map (e.stageMap J K' hJ) ≫ ι.map (stageToSpec D hRS q J (hq J)) =
      ι.map (stageToSpec D' hCS _ K' (hq' K')) ≫
        Space.specSiteObjectMap e.toRingHom hRS hCS q := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 e.toRingHom hJ)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K'.1)) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  have e1 := congrArg (· ≫ formalSpectrumToSpec D hRS q hq) (formalSpectrumMap_spec hR e J K' hJ)
  have e2 : (sY.map (ι.map (e.stageMap J K' hJ)) ≫ formalSpectrumInclusion D (OrderDual.toDual J)) ≫
        formalSpectrumToSpec D hRS q hq =
      sY.map (ι.map (e.stageMap J K' hJ)) ≫ sY.map (ι.map (stageToSpec D hRS q J (hq J))) :=
    (Category.assoc _ _ _).trans
      (congrArg (sY.map (ι.map (e.stageMap J K' hJ)) ≫ ·) (formalSpectrumToSpec_spec D hRS q hq J))
  let i : ι.obj (specOver hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)) ⟶
      ι.obj (specOver hRS q) := Space.specSiteObjectMap e.toRingHom hRS hCS q
  have e3 : sY.map (ι.map (e.stageMap J K' hJ)) ≫ sY.map (ι.map (stageToSpec D hRS q J (hq J))) =
      sY.map (ι.map (stageToSpec D' hCS _ K' (hq' K'))) ≫ sY.map i :=
    (sY.map_comp _ _).symm.trans ((congrArg sY.map hstage).trans (sY.map_comp _ _))
  have e4 := congrArg (· ≫ sY.map i) (formalSpectrumToSpec_spec D' hCS _ hq' K').symm
  exact (Category.assoc _ _ _).symm.trans
    (e1.trans (e2.trans (e3.trans (e4.trans (Category.assoc _ _ _)))))

/-- The generic point of the spectrum of a discrete valuation ring is not its closed point: the
generic point of `Spec R` is the image of the point of `Spec K`, `K` the fraction field, whose
prime ideal is the kernel `0` of `R → K`, while the maximal ideal of `R` is not zero. -/
theorem spec_map_algebraMap_fractionRing_ne_closedPoint (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
        (IsLocalRing.closedPoint (FractionRing R)) ≠ IsLocalRing.closedPoint R := by
  intro h
  have hideal := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap (algebraMap R (FractionRing R))
      (IsLocalRing.maximalIdeal (FractionRing R)) = IsLocalRing.maximalIdeal R at hideal
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R (FractionRing R))]
    at hideal
  exact IsDiscreteValuationRing.not_isField R
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hideal.symm)

/-- The two maps out of the formal spectrum of `C` in the cartesian completion square of
Stacks 0APV agree in `X`. Here `e : R → C` is a continuous homomorphism, `g` is an `R`-point of
`X` restricting to `p : Spf R ⟶ X_{/T}`, and `y` is a `C`-point of `X'` over the `C`-point
`Spec C ⟶ Spec R ⟶ X`; the maps are `Spf C ⟶ Spec C ⟶ X'` and `Spf C ⟶ Spf R ⟶ X_{/T}`. -/
private theorem formalSpectrumToSpec_comp_sheafifiedULiftMap_eq
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    {R C : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing C] [TopologicalSpace C] {I : Ideal R} {I' : Ideal C} (hI : IsAdic I)
    (hI' : IsAdic I') (hR : TopologicalRing.IsWeaklyAdmissible R) {D : QuotientSystem B S hS R}
    {D' : QuotientSystem B S hS C} (e : ContinuousHom D D') (hIe : I.map e.toRingHom ≤ I')
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hCS : B.Contains (Spec (.of C)))
    (hq' : ∀ K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
          (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q) = D'.overS K)
    (p : formalSpectrum D ⟶ Space.completionSheaf B S hS X T)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX)
    (hg : formalSpectrumToSpec D hRS q hq ≫ g = p ≫ completionToUpliftedSheaf X hX T)
    (y : yoneda.obj (siteObject B S hS hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)) ⟶ X')
    (hy : y ≫ f = yoneda.map (Space.specSiteObjectMap e.toRingHom hRS hCS q) ≫
      yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) :
    (formalSpectrumToSpec D' hCS _ hq' ≫
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
          (ULift.up (yonedaEquiv y) : (upliftedSheaf X' hX').obj.obj (Opposite.op
            ((BigAffineFppf.inclusion B S hS).obj
              (specOver hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q))))) ≫
          (ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X' hX'.isSheaf).hom :
            upliftedSheaf X' hX' ⟶ Space.sheafifiedULift B S hS X')) ≫
        Space.sheafifiedULiftMap B S hS f =
      (formalSpectrumMap hR e ≫ p) ≫ Space.completionSheafInclusion B S hS X T := by
  let i : (BigAffineFppf.inclusion B S hS).obj
        (specOver hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)) ⟶
      (BigAffineFppf.inclusion B S hS).obj (specOver hRS q) :=
    Space.specSiteObjectMap e.toRingHom hRS hCS q
  let yC : (upliftedSheaf X' hX').obj.obj (Opposite.op ((BigAffineFppf.inclusion B S hS).obj
      (specOver hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)))) :=
    ULift.up (yonedaEquiv y)
  let fU : upliftedSheaf X' hX' ⟶ upliftedSheaf X hX :=
    ObjectProperty.homMk (Functor.whiskerRight f uliftFunctor.{u + 1})
  have hiso : ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X' hX'.isSheaf).hom ≫
        Space.sheafifiedULiftMap B S hS f =
      fU ≫ ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X hX.isSheaf).hom := by
    apply ObjectProperty.hom_ext
    exact (Space.whiskerRight_comp_sheafifiedULiftIso_hom B S hS hX'.isSheaf hX.isSheaf f).symm
  have hfy : f.app _ (yonedaEquiv y) =
      X.map i.op (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down := by
    have := congrArg yonedaEquiv hy
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map] at this
  have h1 : fU.hom.app _ yC = (upliftedSheaf X hX).obj.map i.op
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g) := congrArg ULift.up hfy
  have hleft : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm yC ≫ fU =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i ≫ g := by
    refine (Sheaf.sectionEquiv_symm_comp (BigFppfOver.topology B S hS) fU yC).symm.trans ?_
    refine (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (X := (BigAffineFppf.inclusion B S hS).obj
        (specOver hCS (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)))
      (F := upliftedSheaf X hX)).symm h1).trans ?_
    refine (Sheaf.sectionEquiv_symm_map (BigFppfOver.topology B S hS) i _).trans ?_
    exact congrArg (_ ≫ ·)
      ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm_apply_apply g)
  have ha : (formalSpectrumToSpec D' hCS _ hq' ≫
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm yC ≫
          (ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X' hX'.isSheaf).hom :
            upliftedSheaf X' hX' ⟶ Space.sheafifiedULift B S hS X')) ≫
        Space.sheafifiedULiftMap B S hS f =
      formalSpectrumToSpec D' hCS _ hq' ≫
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i ≫ g) ≫
          ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X hX.isSheaf).hom := by
    rw [Category.assoc, Category.assoc, hiso, ← Category.assoc _ fU, hleft]
  have hb : (formalSpectrumMap hR e ≫ p) ≫ Space.completionSheafInclusion B S hS X T =
      (formalSpectrumMap hR e ≫ formalSpectrumToSpec D hRS q hq) ≫ g ≫
        ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X hX.isSheaf).hom := by
    rw [completionSheafInclusion_eq_comp hX, Category.assoc, ← Category.assoc p, ← hg,
      Category.assoc, Category.assoc]
  rw [formalSpectrumMap_comp_formalSpectrumToSpec hI hI' hR e hIe hRS q hq hCS hq'] at hb
  refine ha.trans (hb.trans ?_).symm
  simp only [Category.assoc]
  rfl

/-- An `R`-point `s` of `X`, for `R` a complete discrete valuation ring, whose inverse image of
`T` lies over the closed point has its generic point outside `T`: the generic point of `Spec R`
is not its closed point. -/
private theorem genericFieldValuedPoint_class_notMem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsNoetherianCompleteLocalRing R) (T : Set (Space.points B S hS X))
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (s : X.obj (op ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q))))
    (hs : PreimageSubsetClosedPoint hR T hRS q s) :
    (Space.genericFieldValuedPoint hRS q s).class B S hS X ∉ T := by
  intro hmem
  let w : Space.FieldValuedPoint B S hS (yoneda.obj (siteObject B S hS hRS q)) :=
    ⟨FractionRing R, Space.contains_spec_fractionRing hRS,
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ q,
      Space.specSiteObjectMap (algebraMap R (FractionRing R)) hRS
        (Space.contains_spec_fractionRing hRS) q⟩
  have hw : Space.pointsToScheme B S hS (siteObject B S hS hRS q)
      (w.class B S hS _) = IsLocalRing.closedPoint R := hs hmem
  exact spec_map_algebraMap_fractionRing_ne_closedPoint R hw

/-- **Stacks 0AQW.** In the situation of Stacks 0GDB, let `f : X' ⟶ X` be a proper morphism of
algebraic spaces over `S`, let `T` be a closed set of points of `X`, and let the restriction
`U' ⟶ U` of `f` to the open complements of `T` and of `T' = |f|⁻¹ T` be surjective. Then the
morphism of completions `f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-surjective.

An adic morphism `p : Spf R ⟶ X_{/T}` out of a complete discrete valuation ring `R` algebraizes
by Stacks 0GBU to a morphism `Spec R ⟶ X` whose fibre over `T` is the closed point, so its
generic point lies over `U`. The valuative step
`AlgebraicGeometry.Space.exists_isExtension_lift_of_isProper_of_isSurjective` (Stacks 00PH,
0A40 and 0AP1) produces an extension `R ⊂ R'` of complete discrete valuation rings and a point
`Spec R' ⟶ X'` over `Spec R' ⟶ Spec R ⟶ X`. Restricted to `Spf R'` and paired with
`Spf R' ⟶ Spf R ⟶ X_{/T}`, it lands in `X'_{/T'}` because the completion square of Stacks 0APV
is cartesian, and this is the lift.

The source also assumes `X` locally Noetherian, so that `f_{/T}` is a morphism of locally
Noetherian formal algebraic spaces and the algebraization of Stacks 0GBU is available as stated;
neither use is needed here, and the statement is proved without that hypothesis. -/
@[stacks 0AQW]
theorem isRigSurjective_completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T) (hf : Space.IsProper B S hS f)
    (hsurj : Space.IsSurjective B S hS
      ((Space.openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f)) :
    IsRigSurjective B S hS (Space.completionSheafMap B S hS f T) := by
  intro R _ _ _ _ _ _ hadic hcomplete hRweak D p hp
  have hRN : IsNoetherianCompleteLocalRing R := ⟨inferInstance, inferInstance, hcomplete⟩
  have hRS : B.Contains (Spec (.of R)) := contains_spec_of_quotientSystem hadic hcomplete D
  obtain ⟨q, hq⟩ := exists_specHom_compatible_overS hadic
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime hcomplete D
  have hD₁ := exists_pow_le_of_isWeakIdealOfDefinition hadic
  have hD := exists_weakIdealOfDefinition_le_pow hadic
  -- the algebraization of `p`, by Stacks 0GBU
  obtain ⟨g, hg⟩ := surjective_map_into_algebraicSpace hRN D hD₁ hD hRS q hq X hX
    (p ≫ completionToUpliftedSheaf X hX T)
  have hsub := preimageSubsetClosedPoint_of_comp_eq hRN D hD₁ hD hRS q hq hX T hT hp hg
  let s : X.obj (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q))) :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down
  -- the valuative step: an extension `R ⊂ C` and a `C`-point of `X'` over it
  obtain ⟨C, _, _, _, _, _, _, _, _, hCadic, hCcomplete, hCS, y, hy⟩ :=
    Space.exists_isExtension_lift_of_isProper_of_isSurjective hX' hX f T hf hsurj R hRS q s
      (genericFieldValuedPoint_class_notMem hRN T hRS q s hsub)
  let qC : Spec (.of C) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ q
  let D' : QuotientSystem B S hS C := quotientSystemOfSpec hCS qC
  have hmle : (IsLocalRing.maximalIdeal R).map (algebraMap R C) ≤ IsLocalRing.maximalIdeal C :=
    Ideal.map_le_iff_le_comap.mpr (by rw [IsLocalRing.maximalIdeal_comap])
  let e : ContinuousHom D D' :=
    { toRingHom := algebraMap R C
      continuous := continuous_of_isAdic_of_map_le hadic hCadic _ hmle
      overS := fun J K h => by
        rw [← hq J, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          Ideal.quotientMap_comp_mk]
        show _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫ qC
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] }
  -- the lift, through the cartesian completion square of Stacks 0APV
  let yC : (upliftedSheaf X' hX').obj.obj
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (specOver hCS qC))) :=
    ULift.up (yonedaEquiv y)
  let a : formalSpectrum D' ⟶ Space.sheafifiedULift B S hS X' :=
    formalSpectrumToSpec D' hCS qC (quotientSystemOfSpec_overS hCS qC) ≫
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm yC ≫
        ObjectProperty.homMk (Space.sheafifiedULiftIso B S hS X' hX'.isSheaf).hom
  let b : formalSpectrum D' ⟶ Space.completionSheaf B S hS X T :=
    formalSpectrumMap hRweak e ≫ p
  have hab : a ≫ Space.sheafifiedULiftMap B S hS f =
      b ≫ Space.completionSheafInclusion B S hS X T :=
    formalSpectrumToSpec_comp_sheafifiedULiftMap_eq hX' hX f T hadic hCadic hRweak e hmle hRS q
      hq hCS (quotientSystemOfSpec_overS hCS qC) p g hg y hy
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hCadic, hCcomplete, D', e,
    (Space.isPullback_completionSheafMap B S hS f T).lift a b hab, rfl,
    (Space.isPullback_completionSheafMap B S hS f T).lift_snd a b hab⟩

end FormalSpace

end AlgebraicGeometry

end
