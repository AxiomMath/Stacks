module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.RingTheory.Module.AdicSystem.PseudoCoherentHomology

/-!
# Killing the homology of a complex at a point from its adic reductions

Let `A` be a Noetherian local ring, `I ⊆ A` a proper ideal and `K` a pseudo-coherent object of
`D(A)`. If `Hⁱ(K ⊗ᴸ_A A/I^t)` vanishes for every `t`, then `Hⁱ(K)` vanishes: the Mittag--Leffler
and completion theorem identifies `AdicCompletion I (Hⁱ(K))` with the inverse limit of those
modules, and a finite module over a Noetherian local ring with vanishing `I`-adic completion is
zero.

For a point `z` of a scheme `W` the same conclusion is reached from vanishing of the
*cohomology sheaves* of the sheaf-level derived tensor products `K ⊗ᴸ_{𝒪_W} 𝓖_t`, once the
stalk at `z` of the sheaf-level derived tensor product is identified with the derived tensor
product over `𝒪_{W,z}`, and once the stalks of the `𝓖_t` are identified with the `𝒪_{W,z}/I^t`.

## Main results

* `Stacks.PseudoCoherent.AdicCompletion.isZero_homology_of_isZero_homology_derivedReduction`:
  over a Noetherian local ring, a pseudo-coherent complex whose adic reductions have vanishing
  `i`-th homology has vanishing `Hⁱ`.
* `AlgebraicGeometry.isZero_homology_derivedStalk_of_isZero_homology`: the stalk at `z` of a
  vanishing cohomology sheaf vanishes.
* `AlgebraicGeometry.isZero_homology_derivedStalk_of_isZero_homology_sheafTensor`: the previous
  two combined — vanishing of the cohomology sheaves of the sheaf-level derived tensor products
  kills `Hⁱ(K_z)`.
* `Stacks.DerivedTensor.ExactFunctorComparison.nonempty_mapDerivedCategory_derivedTensor_iso` and
  `AlgebraicGeometry.nonempty_derivedStalk_derivedTensor_iso`: an exact functor to modules —
  in particular the stalk at `z` — carries a derived tensor product to the derived tensor
  product over the target ring, given the corresponding statement for the total tensor complex.
* `AlgebraicGeometry.isZero_homology_derivedStalk_of_isZero_homology_tensorComplex`: the same
  vanishing conclusion, with only the underived comparison carried.
* `AlgebraicGeometry.isPseudoCoherent_derivedStalk_of_finite_stalk_homology`: over a Noetherian
  stalk ring, `K_z` is pseudo-coherent as soon as the cohomology sheaves of `K` vanish in large
  degrees and all have finite stalks at `z`.

## Implementation notes

*The model of the derived categories.* Everything is read at `HasDerivedCategory.standard`,
activated as a local instance. That is forced on the ring side: both
`CochainComplex.DerivedTensor.DerivedTensorProduct` and
`StacksDraft.PseudoCoherence.IsPseudoCoherent` are stated at that model, and a statement proved
for one model says nothing about another. On the sheaf side it is the model
`AlgebraicGeometry.fourierMukai` and the bands of [Stacks, Tag 0FZ9] are stated at, so no
comparison of models is needed anywhere below.

*The two derived tensor products, and the hypothesis relating them.* Neither derived tensor
product is canonical in the statements below: the ring-level one is the structure
`CochainComplex.DerivedTensor.DerivedTensorProduct 𝒪_{W,z}` that the Mittag--Leffler and
completion theorem consumes, and the sheaf-level one is an arbitrary bifunctor `T` on
`D(𝒪_W)` — the shape in which [Stacks, Tag 06YU] supplies it, and the shape
`AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk` already takes it. The
isomorphism

`((T.obj E).obj F)_z ≅ E_z ⊗ᴸ_{𝒪_{W,z}} F_z`

between the stalk of the sheaf-level derived tensor product and the ring-level one is therefore
a hypothesis, the derived form of [Stacks, Tag 01CB]; it is quantified over both of its
arguments and mentions no interval, no vanishing and no particular complex. It is the same
hypothesis `AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk` carries, with
the stalk-level bifunctor pinned to the one of the `DerivedTensorProduct` structure rather than
left arbitrary.

*How much of that hypothesis is genuinely needed.* Only its underived form. If `P` is a K-flat
complex of `𝒪_W`-modules and `Tot` computes the sheaf-level derived tensor product of `P` with
an arbitrary complex `L` — which is what [Stacks, Tag 06YU] provides, the left factor alone
being K-flat — then the derived comparison follows from the single isomorphism of complexes of
`𝒪_{W,z}`-modules

`Tot_z ≅ Tot(P_z ⊗_{𝒪_{W,z}} L_z)`.

The two remaining ingredients are discharged: the stalk of a K-flat complex is K-flat
(`AlgebraicGeometry.kFlat_modulesStalkFunctor`, the stalk criterion of [Stacks, Tag 06YB]), and
a K-flat left factor computes a packaged ring-level derived tensor product against an arbitrary
right factor (`CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat`), which
is what allows the right factor `𝒪_{W,z}/I^t` — not flat — to be fed to the comparison.

*What is proved outright.* The ring-level statement, which is where the mathematics is: the
limit of a pointwise zero inverse system is zero, so the completion of `Hⁱ(K)` vanishes, and a
finite module over a Noetherian local ring is Hausdorff for any proper ideal
(`IsHausdorff.of_isLocalRing`), so it injects into its completion. Finiteness of `Hⁱ(K)` is the
Noetherian characterisation of pseudo-coherence. On the sheaf side what is proved outright is
the passage between the cohomology sheaves of `K` and the homology of `K_z`, which is the
comparison `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for the exact stalk functor.

## References

* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.PseudoCoherent.AdicCompletion

/-- **Adic reductions detect the homology of a pseudo-coherent complex over a Noetherian local
ring.** Let `I` be a proper ideal of a Noetherian local ring `A` and let `K` be a pseudo-coherent
object of `D(A)`. If `Hⁱ(K ⊗ᴸ_A A/I^(t+1))` vanishes for every `t`, then `Hⁱ(K)` vanishes. -/
theorem isZero_homology_of_isZero_homology_derivedReduction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hvan : ∀ t : ℕ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((T.tensor.obj K).obj
        ((NoetherianAdicCompletion.idealPowerQuotientSystem I).obj (Opposite.op t))))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  have hfin : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
    (((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      K i A).2.1).mp hK).2 i
  obtain ⟨-, ⟨e⟩⟩ := pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction
    A I K T hK i
  have hzf : IsZero ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
    Functor.isZero _ fun n => hvan n.unop
  have hlim := (limit.isLimit
    ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)).isZero_pt hzf
  have hac := hlim.of_iso e
  have : IsHausdorff I ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
    IsHausdorff.of_isLocalRing I _ hI
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => AdicCompletion.of_injective I _ ?_⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp hac).elim _ _

end Stacks.PseudoCoherent.AdicCompletion

namespace Stacks.DerivedTensor.ExactFunctorComparison

/-- **An exact functor to modules carries a derived tensor product to the derived tensor product
over the target ring, as soon as it carries the total tensor complex there and the image of the
left factor is K-flat.** Here `cmpL` says that the total complex `Tot` computes the source
derived tensor product of `P` and `L`, and `htot` says that `F` carries `Tot` to the total
tensor complex of the images of `P` and `L`.

The K-flat comparison on the target is the one-sided one, so no flatness is required of `L`. -/
theorem nonempty_mapDerivedCategory_derivedTensor_iso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [CommRing B] (F : A ⥤ ModuleCat.{u} B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (TA : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (TB : CochainComplex.DerivedTensor.DerivedTensorProduct B)
    (P L Tot : CochainComplex A ℤ)
    (cmpL : (TA.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj Tot)
    (htot : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Tot ≅
      MonoidalCategory.tensorObj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
    (hkf : CochainComplex.KFlat.{u, u}
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    Nonempty (F.mapDerivedCategory.obj
        ((TA.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L)) ≅
      (TB.tensor.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).obj
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L))) := by
  obtain ⟨cmpB⟩ := CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat TB
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) hkf
  refine ⟨F.mapDerivedCategory.mapIso cmpL ≪≫ F.mapDerivedCategoryFactors.app Tot ≪≫
    DerivedCategory.Q.mapIso htot ≪≫ cmpB.symm ≪≫
    (TB.tensor.mapIso (F.mapDerivedCategoryFactors.app P).symm).app _ ≪≫
    (TB.tensor.obj _).mapIso (F.mapDerivedCategoryFactors.app L).symm⟩

end Stacks.DerivedTensor.ExactFunctorComparison

namespace AlgebraicGeometry

variable {W : Scheme.{u}} (z : W)

/-- **The derived form of [Stacks, Tag 01CB] at a point, from its underived form on total
complexes.** Let `P` be a K-flat complex of `𝒪_W`-modules, `L` an arbitrary one, `Tot` a complex
computing their sheaf-level derived tensor product, and `𝒯` a derived tensor product on
`D(𝒪_{W,z})`. If the stalk at `z` carries `Tot` to the total tensor complex of the stalks of `P`
and `L`, then it carries the sheaf-level derived tensor product of `P` and `L` to the derived
tensor product of their stalks over `𝒪_{W,z}`. -/
theorem nonempty_derivedStalk_derivedTensor_iso
    (T : DerivedCategory W.Modules ⥤ DerivedCategory W.Modules ⥤ DerivedCategory W.Modules)
    (𝒯 : CochainComplex.DerivedTensor.DerivedTensorProduct (W.presheaf.stalk z))
    (P L Tot : CochainComplex W.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex W.toSheafedSpace P)
    (cmpL : (T.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj Tot)
    (htot : ((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Tot ≅
      MonoidalCategory.tensorObj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) :
    Nonempty ((derivedStalkFunctor z).obj
        ((T.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L)) ≅
      (𝒯.tensor.obj ((derivedStalkFunctor z).obj (DerivedCategory.Q.obj P))).obj
        ((derivedStalkFunctor z).obj (DerivedCategory.Q.obj L))) :=
  Stacks.DerivedTensor.ExactFunctorComparison.nonempty_mapDerivedCategory_derivedTensor_iso
    (Stacks.ModuleSkyscraper.modulesStalkFunctor W z) T 𝒯 P L Tot cmpL htot
    (kFlat_modulesStalkFunctor z P hP)

/-- **The stalk of a vanishing cohomology sheaf vanishes.** If the `i`-th cohomology sheaf of an
object `X` of `D(𝒪_W)` is zero, then the `i`-th homology of its stalk `X_z` over `𝒪_{W,z}` is
zero. -/
theorem isZero_homology_derivedStalk_of_isZero_homology
    (X : DerivedCategory W.Modules) (i : ℤ)
    (hX : IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk z)) i).obj
      ((derivedStalkFunctor z).obj X)) :=
  (Functor.map_isZero (Stacks.ModuleSkyscraper.modulesStalkFunctor W z) hX).of_iso
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapDerivedCategoryHomologyIso i).app X)

/-- A derived tensor product of stalks has vanishing homology if the stalk of a vanishing object
is isomorphic to it. -/
private theorem isZero_homology_tensor_of_iso_derivedStalk
    (𝒯 : CochainComplex.DerivedTensor.DerivedTensorProduct (W.presheaf.stalk z))
    (X K F : DerivedCategory W.Modules) (G : DerivedCategory (ModuleCat.{u} (W.presheaf.stalk z)))
    (i : ℤ) (hX : IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj X))
    (e : (derivedStalkFunctor z).obj X ≅
      (𝒯.tensor.obj ((derivedStalkFunctor z).obj K)).obj ((derivedStalkFunctor z).obj F))
    (h : (derivedStalkFunctor z).obj F ≅ G) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk z)) i).obj
      ((𝒯.tensor.obj ((derivedStalkFunctor z).obj K)).obj G)) :=
  (isZero_homology_derivedStalk_of_isZero_homology z X i hX).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      (((𝒯.tensor.obj _).mapIso h).symm ≪≫ e.symm))

/-- **Pseudo-coherence of a stalk from finiteness of the stalks of the cohomology sheaves.** If
the cohomology sheaves of `K` vanish in all large degrees and each has a finite stalk at `z`
over the Noetherian ring `𝒪_{W,z}`, then `K_z` is a pseudo-coherent object of
`D(𝒪_{W,z})`. -/
theorem isPseudoCoherent_derivedStalk_of_finite_stalk_homology
    [IsNoetherianRing (W.presheaf.stalk z)] (K : DerivedCategory W.Modules)
    (hbdd : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj K))
    (hfin : ∀ i : ℤ, Module.Finite (W.presheaf.stalk z)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj K))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedStalkFunctor z).obj K) := by
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((derivedStalkFunctor z).obj K) 0 (W.presheaf.stalk z)).2.1).mpr ⟨?_, fun i => ?_⟩
  · obtain ⟨b, hb⟩ := hbdd
    exact ⟨b, fun i hi => isZero_homology_derivedStalk_of_isZero_homology z K i (hb i hi)⟩
  · have : Module.Finite (W.presheaf.stalk z)
        ((DerivedCategory.homologyFunctor W.Modules i ⋙
          Stacks.ModuleSkyscraper.modulesStalkFunctor W z).obj K) := hfin i
    exact Module.Finite.equiv
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapDerivedCategoryHomologyIso
        i).app K).toLinearEquiv.symm

/-- **Sheaf-level adic reductions kill the homology of the stalk.** Let `z` be a point of a
scheme `W` with Noetherian local ring `𝒪_{W,z}`, let `T` be a derived tensor product on
`D(𝒪_W)` and let `𝒯` be one on `D(𝒪_{W,z})`. Let `I ⊆ 𝒪_{W,z}` be a proper ideal and let
`𝓖 : ℕ → D(𝒪_W)` have stalks the reductions `𝒪_{W,z}/I^(t+1)`. If `K_z` is pseudo-coherent and
the `i`-th cohomology sheaf of `T(K, 𝓖 t)` vanishes for every `t`, then `Hⁱ(K_z) = 0`.

The hypothesis `hstalk` is the derived form of [Stacks, Tag 01CB]: taking the stalk at `z`
carries the sheaf-level derived tensor product to the ring-level one. -/
theorem isZero_homology_derivedStalk_of_isZero_homology_sheafTensor
    [IsNoetherianRing (W.presheaf.stalk z)]
    (T : DerivedCategory W.Modules ⥤ DerivedCategory W.Modules ⥤ DerivedCategory W.Modules)
    (𝒯 : CochainComplex.DerivedTensor.DerivedTensorProduct (W.presheaf.stalk z))
    (hstalk : ∀ E F : DerivedCategory W.Modules,
      (derivedStalkFunctor z).obj ((T.obj E).obj F) ≅
        (𝒯.tensor.obj ((derivedStalkFunctor z).obj E)).obj ((derivedStalkFunctor z).obj F))
    (I : Ideal (W.presheaf.stalk z)) (hI : I ≠ ⊤) (𝓖 : ℕ → DerivedCategory W.Modules)
    (h𝓖 : ∀ t : ℕ, (derivedStalkFunctor z).obj (𝓖 t) ≅
      (NoetherianAdicCompletion.idealPowerQuotientSystem I).obj (Opposite.op t))
    (K : DerivedCategory W.Modules)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedStalkFunctor z).obj K)) (i : ℤ)
    (hvan : ∀ t : ℕ, IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((T.obj K).obj (𝓖 t)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk z)) i).obj
      ((derivedStalkFunctor z).obj K)) := by
  refine Stacks.PseudoCoherent.AdicCompletion.isZero_homology_of_isZero_homology_derivedReduction
    _ I hI _ 𝒯 hK i fun t => ?_
  exact isZero_homology_tensor_of_iso_derivedStalk z 𝒯 _ _ _ _ i (hvan t) (hstalk K (𝓖 t))
    (h𝓖 t)

/-- **Sheaf-level adic reductions kill the homology of the stalk, with only the underived
comparison carried.** The hypotheses of the previous theorem with the derived form of
[Stacks, Tag 01CB] replaced by its underived form: `P` is a K-flat complex representing the
perfect complex, `Tot t` computes its sheaf-level derived tensor product with `𝓛 t`, and
`htot` says that the stalk at `z` carries `Tot t` to the total tensor complex of the stalks.

The ring-level K-flat comparison and the K-flatness of the stalk of `P` are discharged, not
assumed. -/
theorem isZero_homology_derivedStalk_of_isZero_homology_tensorComplex
    [IsNoetherianRing (W.presheaf.stalk z)]
    (T : DerivedCategory W.Modules ⥤ DerivedCategory W.Modules ⥤ DerivedCategory W.Modules)
    (𝒯 : CochainComplex.DerivedTensor.DerivedTensorProduct (W.presheaf.stalk z))
    (P : CochainComplex W.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex W.toSheafedSpace P)
    (I : Ideal (W.presheaf.stalk z)) (hI : I ≠ ⊤)
    (𝓛 Tot : ℕ → CochainComplex W.Modules ℤ)
    (cmpL : ∀ t : ℕ, (T.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj (𝓛 t)) ≅
      DerivedCategory.Q.obj (Tot t))
    (htot : ∀ t : ℕ, ((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Tot t) ≅
      MonoidalCategory.tensorObj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (𝓛 t)))
    (h𝓛 : ∀ t : ℕ, (derivedStalkFunctor z).obj (DerivedCategory.Q.obj (𝓛 t)) ≅
      (NoetherianAdicCompletion.idealPowerQuotientSystem I).obj (Opposite.op t))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedStalkFunctor z).obj (DerivedCategory.Q.obj P))) (i : ℤ)
    (hvan : ∀ t : ℕ, IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((T.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj (𝓛 t))))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk z)) i).obj
      ((derivedStalkFunctor z).obj (DerivedCategory.Q.obj P))) := by
  refine Stacks.PseudoCoherent.AdicCompletion.isZero_homology_of_isZero_homology_derivedReduction
    _ I hI _ 𝒯 hK i fun t => ?_
  obtain ⟨e⟩ := nonempty_derivedStalk_derivedTensor_iso z T 𝒯 P (𝓛 t) (Tot t) hP (cmpL t) (htot t)
  exact isZero_homology_tensor_of_iso_derivedStalk z 𝒯 _ _ _ _ i (hvan t) e (h𝓛 t)

end AlgebraicGeometry

end
