module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Linear
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.Vanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# The Koszul object of [Stacks, Tag 09IR] restricts to zero off its zero locus

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`. The hypothesis `hKzero` of
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_unit_iff`
(`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/OpenImmersion.lean`) asks that the
sheafified Koszul complex `Stacks.Koszul.Truncation.koszulObject` of the sequence restrict to zero
on the open complement `⋃ᵢ D(f_i)` of its common zero locus. This file proves that, which is the
geometric step that
`StacksFrontier/RingTheory/Koszul/PowerLift/UnitEntry.lean` records as not carried out there.

The route is the one `StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/Vanishing.lean`
sets up: that file reduces the vanishing in the derived category to acyclicity of the complex of
sheaves of modules obtained by sheafifying the Koszul complex termwise and restricting, and
acyclicity of a complex of sheaves of modules is a stalkwise condition
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`, Stacks 01AG).

What makes the stalkwise condition cheap is that no comparison between the stalk of the
sheafified Koszul complex and the Koszul complex of the localized sequence is needed. Only the
*contraction* is transported, not the complex: multiplication by `f_i` is null-homotopic on the
Koszul complex of `f₁, …, f_r` (`Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator`,
Stacks 0663), null-homotopies are preserved by extension of the indexing shape
(`Homotopy.extend`) and by additive functors (`CategoryTheory.Functor.mapHomotopy`), and at a
point `x ∈ D(f_i)` the endomorphism `f_i` induces on the stalk is *invertible* — because the stalk
of `M^~` at `x` is the localization of `M` at the prime `x`
(`AlgebraicGeometry.tilde.toStalk_map`, together with Mathlib's
`IsLocalizedModule` instance for `AlgebraicGeometry.tilde.toStalk`), and `f_i` lies in the
multiplicative set being inverted. A null-homotopic isomorphism makes the identity null-homotopic,
and a complex whose identity is null-homotopic has vanishing homology.

## Main results

* `Stacks.Koszul.OpenComplement.isIso_stalkFunctor_map_tilde_map_smul_id` — on the stalk at a
  point of `D(a)`, the endomorphism of `M^~` induced by multiplication by `a` on `M` is
  invertible. This is the sheaf-level form of the key lever
  `AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen`, in the shape a stalk
  criterion can consume.
* `Stacks.Koszul.OpenComplement.acyclic_restrict_tilde_extend_seqComplex` — the termwise
  sheafified Koszul complex of `f₁, …, f_r`, restricted to `⋃ᵢ D(f_i)`, is acyclic. This is
  exactly the hypothesis of
  `Stacks.Koszul.Truncation.isZero_derivedRestrict_koszulObject_of_acyclic`.
* `Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject` — the hypothesis `hKzero`
  of [Stacks, Tag 09IR] for the affine model, discharged.

## Implementation notes

**The two spellings of the stalk functor on sheaves of modules.** Everything below is phrased
with `Scheme.Modules.toPresheaf (Spec R) ⋙ TopCat.Presheaf.stalkFunctor Ab x` rather than with
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor (Spec R).ringCatSheaf x`, although the
two are equal by `rfl`. The reason is instance synthesis, and it is not cosmetic: the complexes
occurring here live in `HomologicalComplex (Spec R).Modules _`, so `Functor.mapHomotopy` asks for
`Functor.Additive` of a functor whose *source* is spelled `(Spec R).Modules`, and
`stalkAddCommGroupFunctor` is a `def` whose source is spelled `SheafOfModules _`. Synthesis does
not unfold either `def`, so the `Additive` instance found for one spelling is not found for the
other. Writing `toPresheaf (Spec R) ⋙ …` keeps the source in the spelling the complexes use, and
the one instance that has to be supplied by hand is additivity of `Scheme.Modules.toPresheaf`
itself (again a `def`, composed of two functors Mathlib knows to be additive).

For the same reason the point of `Spec R` is taken as an element of the scheme rather than of
`PrimeSpectrum.Top R`: at the latter spelling the `TopCat` in
`TopCat.Presheaf.stalkFunctor` is fixed to `PrimeSpectrum.Top R` and the composite loses even
`PreservesZeroMorphisms`.

**A dedup, deliberately not taken.** `extendMap_smul_id` and `acyclic_of_homotopy_id_zero` below
duplicate existing private declarations: the first is
`StacksFrontier/Homology/DerivedComplete/KoszulTensorVanishing.lean:622` (stated only for
`ComplexShape.embeddingDownNat`; the version here is for an arbitrary embedding), and the second
occurs in `StacksFrontier/Homology/Injectives/KInjective/FunctorialResolution.lean`, for
`CochainComplex C ℤ` only. Reaching the first by `import all` would put
`StacksFrontier/Homology/DerivedComplete/KoszulTensorVanishing.lean` in the import closure, and that
file installs `CategoryTheory.HasDerivedCategory.standard` as a file-level local instance
(line 71); the companion file
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/Vanishing.lean` avoids such an import
for exactly that reason, and the same choice is made here. The four private copies should be
replaced by one public lemma apiece in a separate pass.

No `@[stacks]` attribute is attached: Tag 09IR is the detection statement, which is not proved
here; what is proved is one of its three named inputs.

Everything derived-category-valued is stated at a free `[HasDerivedCategory.{w} _]` binder and
mentions `CategoryTheory.HasDerivedCategory.standard` nowhere, so the results are available at the
locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Koszul.OpenComplement

/-- The forgetful functor from `𝒪_X`-modules to presheaves of abelian groups is additive.
`AlgebraicGeometry.Scheme.Modules.toPresheaf` is a `def`, so synthesis does not see that it is a
composite of two functors Mathlib knows to be additive; this supplies the instance in the
spelling the complexes of this file use. -/
private instance toPresheaf_additive (X : Scheme.{u}) :
    (Scheme.Modules.toPresheaf X).Additive :=
  inferInstanceAs ((SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf X.ringCatSheaf.obj).Additive)

/-- **Multiplication by `a` is invertible on the stalk of `M^~` at a point of `D(a)`.** The stalk
of `M^~` at `x` is the localization of `M` at the prime `x` and the map induced by a module map is
the localized map (`AlgebraicGeometry.tilde.toStalk_map`); since `IsLocalizedModule.map` is linear
in the map, multiplication by `a` on `M` induces multiplication by `a` on the localization, and
that is invertible because `a` avoids `x`.

This is the stalkwise form of
`AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen`. -/
theorem isIso_stalkFunctor_map_tilde_map_smul_id {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (a : R) (x : PrimeSpectrum.Top R)
    (hx : a ∈ x.asIdeal.primeCompl) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf (tilde.map (a • 𝟙 M)))) := by
  have hunit := IsLocalizedModule.map_units (tilde.toStalk M x).hom ⟨a, hx⟩
  rw [Module.End.isUnit_iff] at hunit
  have hsmul : ∀ m : (tilde M).presheaf.stalk x,
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
        (Scheme.Modules.Hom.mapPresheaf (tilde.map (a • 𝟙 M)))) m =
      (algebraMap (R : Type u) (Module.End (R : Type u)
        (ModuleCat.of (R : Type u) ((tilde M).presheaf.stalk x))) a) m := by
    intro m
    rw [tilde.toStalk_map (a • 𝟙 M) x m]
    have h1 : (ModuleCat.Hom.hom (a • 𝟙 M)) = a • (LinearMap.id : M →ₗ[R] M) := by simp
    rw [h1, map_smul, IsLocalizedModule.map_id, Module.algebraMap_end_apply]
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun m₁ m₂ hm => hunit.1 ?_, fun z => ?_⟩
  · exact (hsmul m₁).symm.trans (hm.trans (hsmul m₂))
  · obtain ⟨m, hm⟩ := hunit.2 z
    exact ⟨m, (hsmul m).trans hm⟩

/-- Extending a scalar multiple of the identity along an embedding of complex shapes gives the
same scalar multiple of the identity. In the degrees coming from the source shape the extended
morphism is the original one conjugated by an isomorphism, and in the remaining degrees the
objects are zero. -/
private theorem extendMap_smul_id {R : Type u} [CommRing R] {ι ι' : Type}
    {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex (ModuleCat.{u} R) c)
    (e : c.Embedding c') (a : R) :
    HomologicalComplex.extendMap (a • 𝟙 K) e = a • 𝟙 (K.extend e) := by
  refine HomologicalComplex.hom_ext _ _ fun i' => ?_
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [HomologicalComplex.extendMap_f _ _ hi]
    simp [Linear.smul_comp, Linear.comp_smul]
  · exact (HomologicalComplex.isZero_extend_X K e i' (by tauto)).eq_of_src _ _

/-- A complex whose identity morphism is null-homotopic is acyclic: the identity of every homology
object is the zero morphism. -/
private theorem acyclic_of_homotopy_id_zero {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) (h : Homotopy (𝟙 K) 0) : K.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have hm := h.homologyMap_eq i
  rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at hm

/-- A complex carrying a null-homotopic *invertible* endomorphism is acyclic: composing the
null-homotopy with the inverse makes the identity null-homotopic. -/
private theorem acyclic_of_homotopy_isIso {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K : HomologicalComplex C c} (φ : K ⟶ K) [IsIso φ]
    (h : Homotopy φ 0) : K.Acyclic :=
  acyclic_of_homotopy_id_zero K
    ((Homotopy.ofEq (IsIso.inv_hom_id φ).symm).trans
      ((h.compLeft (inv φ)).trans (Homotopy.ofEq (Limits.comp_zero))))

/-- **The stalk at a point of `D(a)` of a termwise sheafified complex on which multiplication by
`a` is null-homotopic is acyclic.** Both the null-homotopy and the invertibility of the
endomorphism transport: the first through the two additive functors, the second by
`isIso_stalkFunctor_map_tilde_map_smul_id` in each degree. -/
private theorem acyclic_stalk_of_homotopy {R : CommRingCat.{u}} (a : R)
    (x : (Spec R : Scheme.{u})) (hx : x ∈ PrimeSpectrum.basicOpen a)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) (h : Homotopy (a • 𝟙 D) 0) :
    (((Scheme.Modules.toPresheaf (Spec R) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj D)).Acyclic := by
  have hx' : a ∈ Ideal.primeCompl
      (PrimeSpectrum.asIdeal (show PrimeSpectrum (R : Type u) from x)) :=
    (PrimeSpectrum.mem_basicOpen a _).mp hx
  have h3 : Homotopy
      (((Scheme.Modules.toPresheaf (Spec R) ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map (a • 𝟙 D))) 0 :=
    ((Scheme.Modules.toPresheaf (Spec R) ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} x).mapHomotopy
      ((tilde.functor R).mapHomotopy h)).trans (Homotopy.ofEq (by simp))
  have : IsIso ((((Scheme.Modules.toPresheaf (Spec R) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map (a • 𝟙 D)))) := by
    refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun i => ?_
    exact isIso_stalkFunctor_map_tilde_map_smul_id (D.X i) a _ hx'
  exact acyclic_of_homotopy_isIso _ h3

/-- Multiplication by `f i` is null-homotopic on the Koszul complex of `f₁, …, f_r` re-indexed as
a cochain complex in non-positive degrees. This is Stacks 0663 pushed through
`Homotopy.extend`. -/
private theorem homotopy_smul_id_extend_seqComplex {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (i : Fin r) :
    Nonempty (Homotopy (f i • 𝟙 ((Koszul.seqComplex f).extend
      ComplexShape.embeddingDownNat)) 0) := by
  obtain ⟨H⟩ := (Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator f).1 i
  exact ⟨((Homotopy.ofEq (extendMap_smul_id _ _ _).symm).trans
    (H.extend ComplexShape.embeddingDownNat)).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_zero _ _ _))⟩

open Stacks.Koszul.Truncation in
/-- **The termwise sheafified Koszul complex of `f₁, …, f_r` is acyclic on `⋃ᵢ D(f_i)`.** A point
of the open complement of the common zero locus lies in some `D(f_i)`; the stalk there of the
restricted complex is the stalk on `Spec A` at the image point
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), and that stalk complex is acyclic by
`acyclic_stalk_of_homotopy`.

This is exactly the hypothesis of
`Stacks.Koszul.Truncation.isZero_derivedRestrict_koszulObject_of_acyclic`. -/
theorem acyclic_restrict_tilde_extend_seqComplex {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) :
    (((Scheme.Modules.restrictFunctor (openComplement f).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat))).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff]
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (openComplement f).toScheme.ringCatSheaf _).2 fun y => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
  obtain ⟨H⟩ := homotopy_smul_id_extend_seqComplex f i
  refine (ShortComplex.exact_iff_of_iso (ShortComplex.mapNatIso
    ((((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)).sc n)
    (Scheme.Modules.restrictStalkNatIso (openComplement f).ι y))).2
      ((HomologicalComplex.exactAt_iff _ n).1
        (acyclic_stalk_of_homotopy (f i) ((openComplement f).ι y) ?_ _ H n))
  exact (AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of A) (f i)) ▸ hi

open Stacks.Koszul.Truncation Stacks.Duality.OpenImmersion in
/-- **The hypothesis `hKzero` of [Stacks, Tag 09IR], discharged for the affine model.** The
sheafified Koszul object of a finite sequence `f₁, …, f_r` in a commutative ring `A` restricts to
zero on the open complement `⋃ᵢ D(f_i)` of its common zero locus.

This is the input named `hKzero` by
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_unit_iff`, at
`j = (openComplement f).ι` and `K = koszulObject f`, and it is what
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`
(registered for 09IR, implication (2) to (1)) feeds that lemma; through it this theorem reaches the
hypothesis `hunit` of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion`. It is not routed
through `…isWeakTriangulatedGenerator_biprod_of_detection`: that
declaration's hypothesis `hdet` is quantified over all of `D(𝒪_Y)` and is false, as the docstring
of `Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero` records with a
discrete-valuation-ring counterexample, so that declaration is vacuous. -/
theorem isZero_derivedRestrict_koszulObject {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    [HasDerivedCategory.{w} (Spec (CommRingCat.of A)).Modules]
    [HasDerivedCategory.{w} (openComplement f).toScheme.Modules] :
    IsZero ((derivedRestrict (openComplement f).ι).obj (koszulObject f)) :=
  isZero_derivedRestrict_koszulObject_of_acyclic f (acyclic_restrict_tilde_extend_seqComplex f)

end Stacks.Koszul.OpenComplement

end
