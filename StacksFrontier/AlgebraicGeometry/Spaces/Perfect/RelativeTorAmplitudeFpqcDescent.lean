module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
import StacksCore.Tactic.StacksAttribute

/-!
# Fpqc descent of relative Tor amplitude

Let `{g_i : Y_i → Y}` be an fpqc covering of algebraic spaces over a scheme `S`, let
`f : X ⟶ Y` be a morphism of algebraic spaces, and form the cartesian squares

```
X_i --g'_i--> X
|f_i          |f
v             v
Y_i --g_i---> Y
```

Stacks 0DL2 says that an object `E` of `D_QCoh(𝒪_X)` has Tor amplitude in `[a, b]` as an object
of `D(f^{-1}𝒪_Y)` if and only if each `L(g'_i)^* E` has Tor amplitude in `[a, b]` as an object
of `D(f_i^{-1}𝒪_{Y_i})`, and the same with "Tor amplitude in `[a, b]`" replaced by "finite Tor
dimension".

Both clauses are read here at the geometric points of `X`, which is how the source proves them:
Tor dimension can be computed at stalks (Stacks 0DJJ and 04K5), the stalk of `L(g'_i)^* E` at a
geometric point `x̄_i` of `X_i` over `x̄` is the derived base change
`E_{x̄} ⊗^{𝐋}_{𝒪_{X, x̄}} 𝒪_{X_i, x̄_i}`, which Tor independence of `X` and `Y_i` over `Y`
identifies with `E_{x̄} ⊗^{𝐋}_{𝒪_{Y, ȳ}} 𝒪_{Y_i, ȳ_i}` by Stacks 0661, and `𝒪_{Y, ȳ} →
𝒪_{Y_i, ȳ_i}` is faithfully flat because `g_i` is flat and the covering is surjective, so
Stacks 068S descends the bound.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_faithfullyFlat_complex` and
  `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_faithfullyFlat_derived`: Stacks 068S
  at the canonical derived tensor product with the two rings in one universe, for a complex and
  for an arbitrary object of the derived category.
* `AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_restrict_iff_baseChange`:
  the ring-level equivalence behind Stacks 0DL2 — for a pushout square of rings whose two
  intermediate corners are Tor independent over the base and whose covering side is faithfully
  flat, Tor amplitude over the base is *equivalent* to Tor amplitude of the derived base change
  over the covering corner.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_etaleStalk_iff_of_cartesian`:
  **Stacks 0DL2**, the `[a, b]` clause at a geometric point.
* `AlgebraicGeometry.Space.hasFiniteTorDimensionCanonical_etaleStalk_iff_of_cartesian`:
  **Stacks 0DL2**, the finite-Tor-dimension clause at a geometric point.

## Implementation notes

The preservation half of the ring-level equivalence is
`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_torIndependentBaseChange`,
already in the library: the comparison of Stacks 0661 is an isomorphism, so derived extension of
scalars along the covering side carries Tor amplitude over the base to Tor amplitude over the
covering corner. The descent half runs the same isomorphism backwards and then applies Stacks
068S, which needs the covering side to be faithfully flat.

Stacks 068S is available as
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_faithfullyFlat` only with each ring moved
into the module universe by `ULift`, and no identification of `ULift` with extension of scalars
is in the library, so the one-universe form that a stalk computation needs is proved here
instead. It is the composite of the projective-resolution descent
`StacksDraft.TorAmplitude.hasTorAmplitude0DJF_of_faithfullyFlat` with the comparison
`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF` between the two Tor-amplitude
predicates, read at a bounded above complex of projectives: a Tor-amplitude bound over the
faithfully flat extension bounds the cohomology of the base change, hence — extension of scalars
being exact and reflecting vanishing — the cohomology of the complex itself, so the complex is
represented by a bounded above complex of projectives and both sides of the descent are read
there. That is the proof of the private
`StacksDraft.TorAmplitude.hasTorAmplitude_certified_of_faithfullyFlat` of
`StacksFrontier.Homology.TorAmplitude.Local` specialised to the canonical certificates, and is a
dedup target: once that declaration is exported this section should be deleted in favour of it.
The arbitrary-object form is obtained from the complex-level one through a K-flat resolution
(Stacks 06Y4), at which the comparison of a total derived extension of scalars is an
isomorphism.

The geometric statements are the ring-level equivalence instantiated at the *canonical*
homomorphisms of étale local rings of Stacks 04NG, exactly as
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_etaleStalk_of_cartesian` instantiates
Stacks 0DKD; the passage from Tor independence of the algebraic spaces (Stacks 08IP) to Tor
independence of those rings is `AlgebraicGeometry.Space.torIndependent_etaleLocalRing`. The
upper-left corner of the square of étale local rings is the tensor product
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y_i, ȳ_i}` itself, which is what Stacks 0661 is stated for and what
the source's identification of the two derived base changes produces; the library does not
identify `𝒪_{X_i, x̄_i}` with it, and the flat comparison map that
`AlgebraicGeometry.Space.IsEtaleStalkTensorFlat` carries transports the bound in the preservation
direction only. Faithful flatness of `𝒪_{Y, ȳ} → 𝒪_{Y_i, ȳ_i}` is carried as a hypothesis; for a
member of an fpqc covering it is flatness of `g_i` at the image point, which is Stacks 04NG, with
the locality of the canonical homomorphism of étale local rings.

The four étale local rings live in `CommRingCat.{u + 1}`, each being a colimit indexed by the
small étale neighbourhoods of a geometric point, so the ring-level results are instantiated at
`u + 1`; all four lie in the same universe, so
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` applies directly.

## References

* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 068S](https://stacks.math.columbia.edu/tag/068S)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped TensorProduct

universe u

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-! ### Stacks 068S at the canonical derived tensor product, in one universe -/

/-- Tor amplitude at the canonical derived tensor product, with the three certificate arguments
of Stacks 0652 spelled out. Both readings are the flat-representative condition of
Stacks 0654. -/
private theorem hasTorAmplitudeCanonical_iff_explicit {R : Type u} [CommRing R]
    (E : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    HasTorAmplitudeCanonical R E a b ↔
      HasTorAmplitude (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
        (canonicalTensorIsLeftDerived R) E a b :=
  (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R E a b).trans
    (hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) E a b).symm

/-- **Stacks 068S** at the canonical derived tensor product of Stacks 0BYI, with the two rings
and the module carriers in a single universe: if the base change of a complex `K` of
`R`-modules along a faithfully flat `R → S` has Tor amplitude in `[a, b]`, then so does `K`.

A Tor-amplitude bound over `S` bounds the cohomology of the base change of `K`, hence — base
change along a faithfully flat ring map being exact and reflecting vanishing — the cohomology of
`K` itself; so `K` is represented by a bounded above complex `P` of projective modules, whose
base change is again one, and at such complexes Tor amplitude at the canonical derived tensor
product is the projective-resolution Tor amplitude of Stacks 0DJF, which descends. -/
@[ega "IV 2.5.1" "special case",
  sga "4½ Arcata 1.4.2" "more general",
  sga "6 I 5.7" "Exercise 5.7 a)"]
theorem hasTorAmplitudeCanonical_of_faithfullyFlat_complex
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonical S
      (DerivedCategory.Q.obj ((CochainComplex.extendScalars (algebraMap R S)).obj K)) a b) :
    HasTorAmplitudeCanonical R (DerivedCategory.Q.obj K) a b := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars (algebraMap R S)
  have : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
  have : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S))
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  have : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S))
  have hcoh : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (DerivedCategory.Q.obj K)) := by
    intro i hi
    have hz : IsZero
        (((CochainComplex.extendScalars (algebraMap R S)).obj K).homology i) :=
      isZero_homology_of_hasTorAmplitude (canonicalTensorComparison S)
        (canonicalTensorIsLeftDerived S) _ a b
        ((hasTorAmplitudeCanonical_iff_explicit _ a b).1 h) i (Or.inr hi)
    have hzA : IsZero (K.homology i) := by
      rw [← FaithfullyFlat.isZero_extendScalars_iff (B := S) (K.homology i)]
      exact hz.of_iso ((K.sc i).mapHomologyIso F).symm
    exact hzA.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K)
  obtain ⟨P, hproj, hPLE, ⟨eP⟩⟩ :=
    exists_projective_representative_of_isLE (DerivedCategory.Q.obj K) b hcoh
  have := hPLE
  have hflatP : ∀ i : ℤ, Module.Flat R (P.X i) := fun i => by
    have := hproj i
    infer_instance
  have hbddP : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨b, fun i hi => P.isZero_of_isStrictlyLE b i hi⟩
  have hKFlatP : P.KFlat := kFlat_of_isStrictlyLE_projective P b hproj
  let FP : CochainComplex (ModuleCat.{u} S) ℤ :=
    (CochainComplex.extendScalars (algebraMap R S)).obj P
  have hprojFP : ∀ i : ℤ, Projective (FP.X i) :=
    fun i => F.projective_obj_of_projective (hproj i)
  have hzFP : ∀ i : ℤ, b < i → IsZero (FP.X i) :=
    fun i hi => F.map_isZero (P.isZero_of_isStrictlyLE b i hi)
  have hFPLE : FP.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff FP b).2 hzFP
  have := hFPLE
  have hKFlatFP : FP.KFlat := kFlat_of_isStrictlyLE_projective FP b hprojFP
  have hflatFP : ∀ i : ℤ, Module.Flat S (FP.X i) := fun i => by
    have := hprojFP i
    infer_instance
  have hB : HasTorAmplitude (canonicalDerivedTensorProduct S).tensor
      (canonicalTensorComparison S) (canonicalTensorIsLeftDerived S)
      (DerivedCategory.Q.obj FP) a b :=
    (hasTorAmplitude_of_iso ((F.mapDerivedCategoryFactors.app K).symm ≪≫
      F.mapDerivedCategory.mapIso eP ≪≫ F.mapDerivedCategoryFactors.app P) a b).1
        ((hasTorAmplitudeCanonical_iff_explicit _ a b).1 h)
  refine (hasTorAmplitudeCanonical_iff_explicit _ a b).2 ((hasTorAmplitude_of_iso eP a b).2 ?_)
  exact (hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) P hKFlatP hbddP hflatP a b).2
    (hasTorAmplitude0DJF_of_faithfullyFlat P a b
      ((hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison S)
          (canonicalTensorIsLeftDerived S) FP hKFlatFP ⟨b, hzFP⟩ hflatFP a b).1 hB))

/-- **Stacks 068S** at an arbitrary object of `D(R)`: if the total derived extension of scalars
of `E` along a faithfully flat `R → S` has Tor amplitude in `[a, b]`, then so does `E`.

Every object of `D(R)` is the image of a K-flat complex, by Stacks 06Y4, and the comparison of a
total derived extension of scalars with the termwise one is an isomorphism at a K-flat complex,
so this is the complex-level statement transported along that resolution. -/
@[ega "IV 2.5.1" "special case", sga "6 I 5.7" "Exercise 5.7 a)"]
theorem hasTorAmplitudeCanonical_of_faithfullyFlat_derived
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (E : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (h : HasTorAmplitudeCanonical S
      ((totalDerivedExtensionScalars (algebraMap R S)).functor.obj E) a b) :
    HasTorAmplitudeCanonical R E a b := by
  let D := totalDerivedExtensionScalars (algebraMap R S)
  let M := DerivedCategory.Q.objPreimage E
  obtain ⟨P, q, hP, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution M
  have := hq
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  have h₁ : HasTorAmplitudeCanonical S (D.functor.obj (DerivedCategory.Q.obj P)) a b :=
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (D.functor.mapIso eP).symm a b h
  have h₂ : HasTorAmplitudeCanonical S
      (DerivedCategory.Q.obj ((CochainComplex.extendScalars (algebraMap R S)).obj P)) a b :=
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (asIso (D.comparison.app P)) a b h₁
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso eP a b
    (hasTorAmplitudeCanonical_of_faithfullyFlat_complex P a b h₂)

end StacksDraft.TorAmplitude

namespace AlgebraicGeometry.BaseChangeTorAmplitude

open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-! ### The ring-level equivalence -/

/-- The ring-level form of Stacks 0DL2. For a pushout square of commutative rings whose two
intermediate corners `A` and `B` are Tor independent over the base `R`, and whose side `R → B`
is faithfully flat, an object `E` of `D(A)` has Tor amplitude in `[a, b]` over `R` if and only
if its derived base change to the upper-right corner `T` has Tor amplitude in `[a, b]` over `B`.

The forward implication is Tor-independent base change,
`hasTorAmplitudeCanonical_torIndependentBaseChange`: the comparison of Stacks 0661 identifies
derived extension of scalars from `R` to `B` with derived extension of scalars from `A` to `T`
read over `B`. Since that comparison is an isomorphism it also runs backwards, and Stacks 068S
then descends the bound along the faithfully flat `R → B`. -/
theorem hasTorAmplitudeCanonical_restrict_iff_baseChange
    {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
    [IsScalarTower R A T] [IsScalarTower R B T] [Algebra.IsPushout R A B T]
    [Module.FaithfullyFlat R B]
    (hTor : RingTheory.TorIndependence.TorIndependent R A B)
    (E : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ) :
    HasTorAmplitudeCanonical R
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj E) a b ↔
      HasTorAmplitudeCanonical B
        ((ModuleCat.restrictScalars (algebraMap B T)).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars (algebraMap A T)).functor.obj E)) a b := by
  refine ⟨fun hE => hasTorAmplitudeCanonical_torIndependentBaseChange hTor E a b hE, fun hE => ?_⟩
  let Dbase := totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)
  let Dtop := totalDerivedExtensionScalars.{u, u, u} (algebraMap A T)
  let sq : (algebraMap A T).comp (algebraMap R A) = (algebraMap B T).comp (algebraMap R B) :=
    (IsScalarTower.algebraMap_eq R A T).symm.trans (IsScalarTower.algebraMap_eq R B T)
  let cmp :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1,
      u + 1}
    R A B T _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R B) (algebraMap A T) (algebraMap B T)
    sq Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have hcmp : IsIso cmp.2.1 :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u,
      u, u + 1, u + 1, u + 1, u + 1}
    R A B T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hTor Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have hcmpE : IsIso (cmp.2.1.app E) := by
    have : IsIso cmp.2.1 := hcmp
    infer_instance
  have hbase : HasTorAmplitudeCanonical B
      (Dbase.functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj E)) a b :=
    hasTorAmplitudeCanonical_of_iso (asIso (cmp.2.1.app E)).symm a b hE
  exact hasTorAmplitudeCanonical_of_faithfullyFlat_derived _ a b hbase

/-- The finite-Tor-dimension form of the ring-level equivalence behind Stacks 0DL2: under the
same hypotheses, `E` has finite Tor dimension over `R` if and only if its derived base change to
`T` has finite Tor dimension over `B`.

Finite Tor dimension is Tor amplitude in some interval, and the equivalence of intervals is
`hasTorAmplitudeCanonical_restrict_iff_baseChange` for each `[a, b]` separately. -/
theorem hasFiniteTorDimensionCanonical_restrict_iff_baseChange
    {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
    [IsScalarTower R A T] [IsScalarTower R B T] [Algebra.IsPushout R A B T]
    [Module.FaithfullyFlat R B]
    (hTor : RingTheory.TorIndependence.TorIndependent R A B)
    (E : DerivedCategory (ModuleCat.{u} A)) :
    HasFiniteTorDimensionCanonical R
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj E) ↔
      HasFiniteTorDimensionCanonical B
        ((ModuleCat.restrictScalars (algebraMap B T)).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars (algebraMap A T)).functor.obj E)) := by
  rw [hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical,
    hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical]
  exact ⟨fun ⟨a, b, h⟩ =>
      ⟨a, b, (hasTorAmplitudeCanonical_restrict_iff_baseChange hTor E a b).1 h⟩,
    fun ⟨a, b, h⟩ =>
      ⟨a, b, (hasTorAmplitudeCanonical_restrict_iff_baseChange hTor E a b).2 h⟩⟩

end AlgebraicGeometry.BaseChangeTorAmplitude

namespace AlgebraicGeometry.Space

open StacksDraft.TorAmplitude AlgebraicGeometry.BaseChangeTorAmplitude

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stacks 0DL2 -/

/-- **Stacks 0DL2**, the clause on Tor amplitude in `[a, b]`, at a geometric point.

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces whose two morphisms to the base are Tor independent,
let `x̄'` be a geometric point of the upper-left corner, with images `x̄` in `X`, `ȳ'` in `Y'` and
`ȳ` in `Y`, and suppose that the canonical homomorphism `𝒪_{Y, ȳ} → 𝒪_{Y', ȳ'}` of étale local
rings of Stacks 04NG is faithfully flat — which for a member of an fpqc covering it is, being
flat by Stacks 04NG and local. Then an object `E` of `D(𝒪_{X, x̄})` has Tor amplitude in `[a, b]`
over `𝒪_{Y, ȳ}` if and only if its derived base change to
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` has Tor amplitude in `[a, b]` over `𝒪_{Y', ȳ'}`.

This is the source's own proof read at the geometric stalks, where the source reads it: a
relative Tor-amplitude bound is a bound on the stalk complexes over the étale local rings of the
base (Stacks 0DJJ and 04K5), the stalk of `L(g')^* E` is the derived base change of the stalk of
`E`, Tor independence identifies that derived base change over `𝒪_{X, x̄}` with the derived base
change over `𝒪_{Y, ȳ}` by Stacks 0661, and the bound descends along the faithfully flat
`𝒪_{Y, ȳ} → 𝒪_{Y', ȳ'}` by Stacks 068S. The forward implication is Stacks 0DKD (1) at the
tensor product. -/
@[stacks 0DL2 "tor amplitude in [a, b], at a geometric point"]
theorem hasTorAmplitudeCanonical_etaleStalk_iff_of_cartesian
    {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (x' : GeometricPoint B S hS X'.1)
    (E : DerivedCategory (ModuleCat.{u + 1}
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')))) (a b : ℤ) :
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
      (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1)
          (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w)) ≫
        CommRingCat.ofHom
          (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
    Module.FaithfullyFlat
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) →
    letI T := TensorProduct
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
    letI : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
      Algebra.TensorProduct.rightAlgebra
    (HasTorAmplitudeCanonical
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ((ModuleCat.restrictScalars
          (etaleLocalRingMap X.2 f.hom
            (geometricPointMap g'.hom x'))).mapDerivedCategory.obj E) a b ↔
      HasTorAmplitudeCanonical ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
        ((ModuleCat.restrictScalars (algebraMap
            ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T)).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars.{u + 1, u + 1, u + 1} (algebraMap
            ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) T)).functor.obj E))
        a b) := by
  have h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
      CommRingCat.ofHom
        (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  intro hff
  let T := TensorProduct
    ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
    ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
  let : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
    Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra.IsPushout
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
    TensorProduct.isPushout
  let : Module.FaithfullyFlat
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) := hff
  exact hasTorAmplitudeCanonical_restrict_iff_baseChange (T := T)
    (torIndependent_etaleLocalRing f g htor (geometricPointMap g'.hom x')
      (geometricPointMap f'.hom x') h) E a b

/-- **Stacks 0DL2**, the clause on finite Tor dimension, at a geometric point.

Under the hypotheses of `hasTorAmplitudeCanonical_etaleStalk_iff_of_cartesian`, an object `E` of
`D(𝒪_{X, x̄})` has finite Tor dimension over `𝒪_{Y, ȳ}` if and only if its derived base change to
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` has finite Tor dimension over `𝒪_{Y', ȳ'}`. Finite Tor
dimension is Tor amplitude in some interval, so this is the previous statement for each interval
separately — the "elementary topology" with which the source reduces the second clause of the
lemma to the first. -/
@[stacks 0DL2 "finite tor dimension, at a geometric point"]
theorem hasFiniteTorDimensionCanonical_etaleStalk_iff_of_cartesian
    {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (x' : GeometricPoint B S hS X'.1)
    (E : DerivedCategory (ModuleCat.{u + 1}
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')))) :
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
      (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1)
          (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w)) ≫
        CommRingCat.ofHom
          (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
    Module.FaithfullyFlat
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) →
    letI T := TensorProduct
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
    letI : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
      Algebra.TensorProduct.rightAlgebra
    (HasFiniteTorDimensionCanonical
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ((ModuleCat.restrictScalars
          (etaleLocalRingMap X.2 f.hom
            (geometricPointMap g'.hom x'))).mapDerivedCategory.obj E) ↔
      HasFiniteTorDimensionCanonical
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
        ((ModuleCat.restrictScalars (algebraMap
            ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T)).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars.{u + 1, u + 1, u + 1} (algebraMap
            ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) T)).functor.obj E))) := by
  intro hff
  rw [hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical,
    hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical]
  exact ⟨fun ⟨a, b, h⟩ => ⟨a, b, (hasTorAmplitudeCanonical_etaleStalk_iff_of_cartesian
      g' f' f g hpb htor x' E a b hff).1 h⟩,
    fun ⟨a, b, h⟩ => ⟨a, b, (hasTorAmplitudeCanonical_etaleStalk_iff_of_cartesian
      g' f' f g hpb htor x' E a b hff).2 h⟩⟩

end AlgebraicGeometry.Space

end
