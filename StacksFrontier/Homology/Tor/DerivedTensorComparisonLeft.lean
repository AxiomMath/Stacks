module

public import StacksFrontier.Homology.KFlat.AcyclicModule
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedLeft
public import StacksFrontier.Homology.Tor.KFlatResolutionSingleTensor

/-!
# A K-flat left factor computes the derived tensor product of complexes of modules

Let `R` be a commutative ring.  The derived tensor product of complexes of `R`-modules is
computed by the ordinary total tensor product `Tot(K ⊗_R L)` as soon as **one** of the two
complexes is K-flat; the two-sided comparison, which asks both of them to be K-flat, is the
form in which it is usually recorded.  This file supplies the one-sided comparison in the left
variable for complexes of modules, together with its naturality in the arbitrary right
complex.

## Main definitions

* `CochainComplex.DerivedTensor.OneSided.tensorBifunctor` — the derived tensor product of
  complexes of `R`-modules, as the K-flat descent of the total tensor complex.
* `CochainComplex.DerivedTensor.OneSided.comparisonLeft` — **a K-flat left factor computes the
  derived tensor product against an arbitrary right factor**,
  `K ⊗^𝐋_R L ≅ Tot(K ⊗_R L)` in `D(R)` for K-flat `K`.

## Main results

* `CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso` and
  `CochainComplex.DerivedTensor.OneSided.exists_kFlatLeft_quasiIso` — every complex of
  `R`-modules receives a quasi-isomorphism from a complex which is K-flat in either variable
  of the tensor product.
* `CochainComplex.DerivedTensor.OneSided.comparisonLeft_naturality_right` — the one-sided
  comparison is natural in the arbitrary right complex, no flatness being assumed there.
* `CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat` — the same
  statement for the derived tensor product packaged as
  `CochainComplex.DerivedTensor.DerivedTensorProduct`, whose recorded comparison is the
  two-sided one.

## Implementation notes

The derived tensor product appears here as
`CochainComplex.KFlatBifunctor.derivedBifunctor` of the curried tensor product, which is the
form in which the one-sided comparison and its naturality are available; it is the tensor
product of the monoidal structure of `D(R)` by
`CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso`.  Its two localization hypotheses are
the statements that the complexes which are K-flat in one or the other variable localize onto
`D(R)`, and both follow from the K-flat resolutions of Stacks 06Y4 — in the left variable
after `CochainComplex.KFlat.kFlatLeft_of_kFlat`, the symmetry of the tensor product of
modules.  They are supplied as instances, so that the bifunctor and its comparison are the
same terms at every use site: the resolutions are the instances
`CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions` and
`moduleKFlatLocalizerLeft_hasLeftResolutions`, from which
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` and
`kFlatQLeft_isLocalization_of_hasLeftResolutions` give the two localizations.

For `DerivedTensorProduct` the comparison is obtained from a K-flat resolution `P ⟶ L` of the
right factor: the two-sided comparison applies to `(K, P)`, the derived tensor product carries
a quasi-isomorphism to an isomorphism, and `Tot(K ⊗_R P) ⟶ Tot(K ⊗_R L)` is a
quasi-isomorphism because `K` is K-flat.  The choice of resolution is not visible in the
statement, which is why it is recorded as the non-emptiness of the type of such
isomorphisms.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [The Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u w

namespace CochainComplex.DerivedTensor.OneSided

variable (R : Type u) [CommRing R]

/-- **Stacks 06Y4, for the tensor bifunctor.**  Every complex of `R`-modules receives a
quasi-isomorphism from a complex which is K-flat in the second variable of the tensor
product. -/
theorem exists_kFlat_quasiIso (G : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (f : P ⟶ G),
      KFlatBifunctor.KFlat (curriedTensor (ModuleCat.{u} R)) P ∧ QuasiIso f := by
  obtain ⟨P, f, hP, -, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} G
  exact ⟨P, f, hP, hf⟩

/-- **Stacks 06Y4, for the first variable of the tensor bifunctor.**  Every complex of
`R`-modules receives a quasi-isomorphism from a complex which is K-flat in the first variable
of the tensor product. -/
theorem exists_kFlatLeft_quasiIso (G : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (f : P ⟶ G),
      KFlatBifunctor.KFlatLeft (curriedTensor (ModuleCat.{u} R)) P ∧ QuasiIso f := by
  obtain ⟨P, f, hP, hf⟩ := exists_kFlat_quasiIso R G
  exact ⟨P, f, CochainComplex.KFlat.kFlatLeft_of_kFlat.{u, u} hP, hf⟩

/-- **The K-flat resolutions of Stacks 06Y4, as an instance**: `exists_kFlat_quasiIso` in the
form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` takes, so that
`D(R)` is the localization of the complexes of `R`-modules which are K-flat in the second
variable of the tensor product, at the quasi-isomorphisms. -/
instance moduleKFlatLocalizer_hasLeftResolutions :
    (KFlatBifunctor.kFlatLocalizer (curriedTensor (ModuleCat.{u} R))).HasLeftResolutions :=
  KFlatBifunctor.kFlatLocalizer_hasLeftResolutions _ (exists_kFlat_quasiIso R)

/-- **The left K-flat resolutions of Stacks 06Y4, as an instance**: `exists_kFlatLeft_quasiIso`
in the form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization_of_hasLeftResolutions` takes, so that
`D(R)` is the localization of the complexes of `R`-modules which are K-flat in the first
variable of the tensor product, at the quasi-isomorphisms. -/
instance moduleKFlatLocalizerLeft_hasLeftResolutions :
    (KFlatBifunctor.kFlatLocalizerLeft (curriedTensor (ModuleCat.{u} R))).HasLeftResolutions :=
  KFlatBifunctor.kFlatLocalizerLeft_hasLeftResolutions _ (exists_kFlatLeft_quasiIso R)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **The derived tensor product of complexes of `R`-modules**, `- ⊗^𝐋_R -` on `D(R)`,
obtained by descending the total tensor complex along the complexes which are K-flat in
either variable. -/
abbrev tensorBifunctor :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R))

variable {R}

/-- **A K-flat left factor computes the derived tensor product against an arbitrary right
factor**: for K-flat `K` and any `L`, the derived tensor product `K ⊗^𝐋_R L` is the ordinary
total tensor complex `Tot(K ⊗_R L)`. -/
def comparisonLeft (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K) :
    ((tensorBifunctor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  KFlatBifunctor.comparisonLeft (curriedTensor (ModuleCat.{u} R)) K L
    (CochainComplex.KFlat.kFlatLeft_of_kFlat.{u, u} hK)

/-- **The one-sided comparison is natural in the arbitrary right complex**, with no flatness
assumed on either side of the morphism there. -/
theorem comparisonLeft_naturality_right (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ L')
    (hK : CochainComplex.KFlat.{u, u} K) :
    ((tensorBifunctor R).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (comparisonLeft K L' hK).hom =
      (comparisonLeft K L hK).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) g
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)) :=
  KFlatBifunctor.comparisonLeft_naturality_right _ K g _

/-- **The one-sided comparison is natural in the K-flat left complex.** -/
theorem comparisonLeft_naturality_left {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ K')
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (hK' : CochainComplex.KFlat.{u, u} K') :
    ((tensorBifunctor R).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (comparisonLeft K' L hK').hom =
      (comparisonLeft K L hK).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f (𝟙 L)
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)) :=
  KFlatBifunctor.comparisonLeft_naturality_left _ f L _ _

/-! ### The comparison for a packaged derived tensor product -/

section Packaged

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- **A K-flat left factor computes a packaged derived tensor product against an arbitrary
right factor.**  The recorded comparison of `DerivedTensorProduct` asks both complexes to be
K-flat; here the right-hand hypothesis is dropped, at the cost of the isomorphism depending on
a choice of K-flat resolution of the right factor. -/
theorem nonempty_comparisonLeft_of_kFlat (T : DerivedTensorProduct R)
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K) :
    Nonempty ((T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L)) := by
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} L
  have h₁ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have h₂ : IsIso (DerivedCategory.Q.map ((TleftCochain K).map p)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_tleftCochain_map_of_kFlat K hK p hp)
  exact ⟨((T.tensor.obj (DerivedCategory.Q.obj K)).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map p) h₁)).symm ≪≫
    T.comparison K P hK hP ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map ((TleftCochain K).map p)) h₂⟩

end Packaged

end CochainComplex.DerivedTensor.OneSided

end
