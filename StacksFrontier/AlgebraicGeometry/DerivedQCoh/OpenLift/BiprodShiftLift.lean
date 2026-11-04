module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.ShiftedBundleSummand
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulTensorRoof
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.Homology.DerivedCategory.ShiftSummandApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# A perfect object plus its shift is the restriction of a perfect object

Let `X = Spec A` and let `U ⊆ X` be a quasi-compact open. For every perfect object `F` of
`D(𝒪_U)` the object `F ⊕ F[1]` is the restriction of a perfect object of `D(𝒪_X)`.

The argument is three steps. [Stacks, Tag 08EG] produces a perfect `E` on `X` whose restriction
splits as `ℱ[n] ⊕ F` with `ℱ` finite locally free on `U`. [Stacks, Tag 08EH] lifts the idempotent
`(x, y) ↦ (x, 0)` of that splitting to a roof `E ←β— E₁ —γ→ E` of perfect objects on `X` with
`β|_U` invertible, so that `γ|_U` *is* that idempotent after the identification. The cone of `γ`
is then the solution: the identity summand `ℱ[n]` contributes a zero cone, and the cone of the
zero endomorphism of `F` is `F ⊕ F[1]`.

## Main results

* `CategoryTheory.Limits.Biprod.nonempty_iso_biprod_shift_of_distTriang_idempotent`: the cone
  step, in any triangulated category. For `g : Y₁ ⟶ Y` which, under `Y ≅ A ⊞ B` and an
  isomorphism `Y₁ ≅ Y`, is the idempotent `(x, y) ↦ (x, 0)`, any cone of `g` is `B ⊞ B⟦1⟧`.
* `CategoryTheory.Functor.exists_roof_of_natIso_comp`: a roof statement about one restriction
  functor, carried to another that a fully faithful functor compares it with.
* `Stacks.DerivedQCoh.OpenLift.sliceRestrictCompIsoRestrictModules`: the comparison of the
  slice-site model of restriction to `U` with the open-subspace model, on derived categories.
* `Stacks.DerivedQCoh.OpenLift.exists_roof_restrictModules`: [Stacks, Tag 08EH] in the
  open-subspace model.
* `Stacks.DerivedQCoh.OpenLift.exists_unionOfBasicOpens_eq_of_isCompact`: a quasi-compact open of
  `Spec A` is a finite union of basic opens.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_biprod_shift_iso_restrict`: the statement above.

## Implementation notes

**Four models of restriction to `U`, and which this file speaks.** Restriction of `𝒪_X`-modules
to a quasi-compact open is realized four ways in this development, and the two inputs of the
argument are stated in two different ones:

* `AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the functor induced on derived
  categories by the degreewise restriction to the open *subspace*. [Stacks, Tag 08EG] and the
  perfectness of a cone, [Stacks, Tag 08CR], are both stated here, so this is the model the
  conclusion below is stated in.
* `Stacks.Cohomology.OpenSubspace.derivedRestriction`, the *total right derived functor* of the
  same restriction. [Stacks, Tag 08DD] is proved here.
* `Stacks.SheafOfModules.derivedRestrict`, restriction to the opens contained in `U` read on the
  *slice site*. The derived internal hom, the tensor–internal-hom bijection of
  [Stacks, Tag 08J8] and hence [Stacks, Tag 08EH] are stated here.
* the degreewise `(restrictModules X U).mapHomologicalComplex`, which is what the conclusion of
  [Stacks, Tag 08EG] literally writes; `CategoryTheory.Functor.mapDerivedCategoryFactors` is the
  comparison with the first.

The crossing used here composes the two comparisons that are already available:
`Stacks.SheafOfModules.derivedRestrictToSubspaceIso` from the third model to the second, and
`Koszul.DerivedSystem.derivedRestrictionMapIsoOfRingSheaf` from the second to the first.
A *morphism* has to
travel the other way — the idempotent is read off [Stacks, Tag 08EG] in the first model and
handed to [Stacks, Tag 08EH] in the third — which needs the comparison functor to be full, not
merely faithful; that is `Stacks.Injectives.mapDerivedCategory_isEquivalence` applied to
`Stacks.SheafOfModules.sliceToSubspaceFunctor`, which is half of an equivalence of abelian
categories.

**Why the transports are stated abstractly.** `CategoryTheory.Functor.exists_roof_of_natIso_comp`
and the cone lemma mention no scheme. Elaborating the same steps against the concrete functors
exhausts the default heartbeat budget — `rw` with `CategoryTheory.Functor.map_comp` on a morphism
of `D(𝒪_{Spec A})` alone does — while the abstract statements elaborate in the default
budget and are applied once each. No declaration here raises `maxHeartbeats` or `maxRecDepth`.

**The open.** [Stacks, Tag 08EH] is proved at `U = D(f₁) ∪ ⋯ ∪ D(f_r)`, so
`Stacks.DerivedQCoh.OpenLift.exists_roof_restrictModules` is stated there too. The conclusion is
nevertheless stated for an *arbitrary* quasi-compact open, because nothing else in the argument
uses the union form and
`Stacks.DerivedQCoh.OpenLift.exists_unionOfBasicOpens_eq_of_isCompact` supplies the presentation;
the reduction is one substitution. That matters for the consumer: [Stacks, Tag 08EK] applies this
statement at `U ∪ Tᶜ`, which is quasi-compact but not presented as a union of basic opens.

**One type, two instance paths.** `Koszul.DerivedSystem.derivedCat A` and
`Stacks.StrictlyPerfect.OXMod (Spec A).toRingedSpace` are the same type by `rfl`, as are
`(U : (Spec A).Opens).toScheme.Modules` and
`Stacks.StrictlyPerfect.OXMod ((Spec A).toRingedSpace.restrict U.isOpenEmbedding)`. Typeclass
synthesis does not cross between the spellings, so the module universe of
`Stacks.StrictlyPerfect.OXMod` is written out wherever a triangle of the one category is handed
to a lemma stated at the other: that universe is left free by
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished`, and an unascribed
application leaves it a metavariable, which no instance matches. This is bookkeeping, not
mathematics; the same remark applies to [Stacks, Tag 09J5] below, which is stated at the
`Stacks.StrictlyPerfect.OXMod` spelling while the middle object of the roof is built at the
ringed-site one.

## References

* [Stacks Project, Tag 08EI](https://stacks.math.columbia.edu/tag/08EI)
* [Stacks Project, Tag 08EG](https://stacks.math.columbia.edu/tag/08EG)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace
open Koszul.DerivedSystem (affineSite derivedCat unionOfBasicOpens basicOpens
  koszulDerivedSystem HasQuasicoherentCohomology)

universe u

namespace CategoryTheory.Limits.Biprod

/-! ### The cone of the projection onto a summand -/

section Idempotent

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasBinaryBiproducts D]

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- `𝟙_A ⊕ c` with `c = 0` is the idempotent `(x, y) ↦ (x, 0)`, after any reindexing of the
second summand of the source. -/
private lemma map_comp_map_eq_fst_comp_inl {A B W W' : D} (u : W' ⟶ W) {c : W ⟶ B}
    (hc : c = 0) :
    biprod.map (𝟙 A) u ≫ biprod.map (𝟙 A) c = (biprod.fst : A ⊞ W' ⟶ A) ≫ biprod.inl := by
  subst hc
  refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- The square exhibiting a map that is the idempotent `(x, y) ↦ (x, 0)` of `A ⊞ B` as isomorphic,
as an arrow, to `𝟙_A ⊕ c` for a zero `c`. -/
private lemma arrow_comm {A B W Y Y₁ : D} (eY : Y ≅ A ⊞ B) (e₁ : Y₁ ≅ Y) {g : Y₁ ⟶ Y}
    (hg : g = e₁.hom ≫ eY.hom ≫ (biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl ≫ eY.inv)
    (u : B ≅ W) {c : W ⟶ B} (hc : c = 0) :
    (e₁ ≪≫ eY ≪≫ biprod.mapIso (Iso.refl A) u).hom ≫ biprod.map (𝟙 A) c = g ≫ eY.hom := by
  rw [hg]
  simp only [Iso.trans_hom, biprod.mapIso_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  refine (Iso.cancel_iso_hom_left e₁ _ _).2 ((Iso.cancel_iso_hom_left eY _ _).2 ?_)
  exact map_comp_map_eq_fst_comp_inl u.hom hc

/-- **The cone of a map that is the projection onto a summand.** Let `eY : Y ≅ A ⊞ B`, let
`e₁ : Y₁ ≅ Y`, and let `g : Y₁ ⟶ Y` be, after those two identifications, the idempotent
`(x, y) ↦ (x, 0)` of `A ⊞ B`. Then any cone of `g` is isomorphic to `B ⊞ B⟦1⟧`.

The identity summand `A` contributes a zero cone and the cone of the zero endomorphism of `B` is
`B ⊞ B⟦1⟧`, so only the second summand survives, doubled. The first half is
`CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_map_id`; the second is the inverse
rotation of the split triangle of `B` and `B⟦1⟧`, whose third morphism is zero, so that the
inverse rotation's first morphism is the zero endomorphism of `B`. -/
theorem nonempty_iso_biprod_shift_of_distTriang_idempotent {A B Y Y₁ Z : D} (eY : Y ≅ A ⊞ B)
    (e₁ : Y₁ ≅ Y) {g : Y₁ ⟶ Y}
    (hg : g = e₁.hom ≫ eY.hom ≫ (biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl ≫ eY.inv)
    {v : Y ⟶ Z} {w : Z ⟶ Y₁⟦(1 : ℤ)⟧} (hT : Triangle.mk g v w ∈ distTriang D) :
    Nonempty (Z ≅ B ⊞ B⟦(1 : ℤ)⟧) := by
  have hT' : (binaryBiproductTriangle B (B⟦(1 : ℤ)⟧)).invRotate ∈ distTriang D :=
    inv_rot_of_distTriang _ (binaryBiproductTriangle_distinguished B (B⟦(1 : ℤ)⟧))
  have hzero : (binaryBiproductTriangle B (B⟦(1 : ℤ)⟧)).invRotate.mor₁ = 0 := by
    -- the two spellings of the zero morphism of a preadditive category are closed by `rfl`
    simp [binaryBiproductTriangle]
    rfl
  let u : B ≅ (binaryBiproductTriangle B (B⟦(1 : ℤ)⟧)).invRotate.obj₁ :=
    (shiftEquiv D (1 : ℤ)).unitIso.app B
  obtain ⟨Z₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle
    (biprod.map (𝟙 A) (binaryBiproductTriangle B (B⟦(1 : ℤ)⟧)).invRotate.mor₁)
  obtain ⟨e₀⟩ := nonempty_iso_of_distTriang_biprod_map_id _ hT₀ hT'
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ hT hT₀
    (Arrow.isoMk _ _ (arrow_comm eY e₁ hg u hzero))
  exact ⟨Triangle.π₃.mapIso e ≪≫ e₀⟩

end Idempotent

end CategoryTheory.Limits.Biprod

namespace CategoryTheory.Functor

/-- **Transport of a roof statement along a fully faithful comparison of two functors.** Let
`R₃ : C ⥤ D₂` and `R₁ : C ⥤ D₁` be functors out of one category, compared by a fully faithful
`Φ : D₂ ⥤ D₁` through `θ : R₃ ⋙ Φ ≅ R₁`. If every morphism `R₃ E ⟶ R₃ E'` fits into a roof
`E ←β— X i —γ→ E'` with `R₃ β` invertible and `R₃ γ = R₃ β ≫ (that morphism)`, then so does
every morphism `R₁ E ⟶ R₁ E'`.

Fullness is what produces a morphism in the `R₃` model from the given one in the `R₁` model;
the rest is the naturality of `θ` at `β` and at `γ`. The predicate `p` on the index is carried
along untouched, so a clause about the middle object of the roof survives the transport. -/
theorem exists_roof_of_natIso_comp {C D₁ D₂ : Type*} [Category C] [Category D₁] [Category D₂]
    (R₁ : C ⥤ D₁) (R₃ : C ⥤ D₂) (Φ : D₂ ⥤ D₁) [Φ.Full] [Φ.Faithful] (θ : R₃ ⋙ Φ ≅ R₁)
    {ι : Type*} (X : ι → C) (p : ι → Prop) (E E' : C)
    (h : ∀ α : R₃.obj E ⟶ R₃.obj E', ∃ (i : ι) (β : X i ⟶ E) (γ : X i ⟶ E'),
      p i ∧ IsIso (R₃.map β) ∧ R₃.map γ = R₃.map β ≫ α)
    (α : R₁.obj E ⟶ R₁.obj E') :
    ∃ (i : ι) (β : X i ⟶ E) (γ : X i ⟶ E'),
      p i ∧ IsIso (R₁.map β) ∧ R₁.map γ = R₁.map β ≫ α := by
  obtain ⟨i, β, γ, hp, hβ, hγ⟩ := h (Φ.preimage (θ.hom.app E ≫ α ≫ θ.inv.app E'))
  refine ⟨i, β, γ, hp, ?_, ?_⟩
  · have := hβ
    refine (NatIso.isIso_map_iff θ β).mp ?_
    rw [Functor.comp_map]
    infer_instance
  · rw [← NatIso.naturality_1 θ γ, ← NatIso.naturality_1 θ β, Functor.comp_map, Functor.comp_map,
      hγ, Functor.map_comp, Functor.map_preimage]
    simp

end CategoryTheory.Functor

namespace Stacks.DerivedQCoh.OpenLift

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ}

/-! ### Crossing from the slice-site model of restriction to the open-subspace one -/

/-- The slice-site and open-subspace models of `𝒪_U`-modules have equivalent derived categories:
they are equivalent abelian categories, and an additive equivalence of abelian categories induces
an equivalence of derived categories. Being an equivalence, the comparison is *full*, which is
what carries a morphism from the open-subspace model back to the slice one. -/
theorem isEquivalence_sliceToSubspace_mapDerivedCategory (U : (Spec A).Opens) :
    (Stacks.SheafOfModules.sliceToSubspaceFunctor (Spec A).sheaf
      U).mapDerivedCategory.IsEquivalence :=
  let : (Stacks.SheafOfModules.sliceToSubspaceFunctor (Spec A).sheaf U).IsEquivalence :=
    inferInstanceAs (U.sheafOfModulesEquivOver
      (_root_.structureSheaf (Spec A).sheaf)).functor.IsEquivalence
  Stacks.Injectives.mapDerivedCategory_isEquivalence _

/-- **Restriction to `U` on derived categories, read through the slice site, is restriction to
the open subspace `U`.** This is `Stacks.SheafOfModules.derivedRestrictToSubspaceIso` — which
lands at the total right derived functor of restriction — followed by
`Koszul.DerivedSystem.derivedRestrictionMapIsoOfRingSheaf`, which identifies that with the
functor induced degreewise. -/
def sliceRestrictCompIsoRestrictModules (U : (Spec A).Opens) :
    Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf U ⋙
        (Stacks.SheafOfModules.sliceToSubspaceFunctor (Spec A).sheaf U).mapDerivedCategory ≅
      AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace U :=
  Stacks.SheafOfModules.derivedRestrictToSubspaceIso (Spec A).sheaf _ ≪≫
    Koszul.DerivedSystem.derivedRestrictionMapIsoOfRingSheaf _ _

/-- **[Stacks, Tag 08EH] with the restriction functor named as
`Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf U`.** The same statement as
`Koszul.DerivedSystem.exists_roof_tensorKoszul`, which names the functor
`Stacks.Cohomology.SliceDerivedSheafHom.restrictD (affineSite A) U` and the objects at the
ringed-site spelling `Koszul.DerivedSystem.affineDerivedCat A` of the module category; the two
functors and the two spellings are definitionally equal, and this declaration is where that
crossing is paid, in term mode, once.

It is the spelling `sliceRestrictCompIsoRestrictModules` is stated at, so that the hypothesis
of `CategoryTheory.Functor.exists_roof_of_natIso_comp` below is met by this statement without a
further crossing. Performing this crossing inside the unification of that hypothesis instead
exhausts the default heartbeat budget. -/
private theorem exists_roof_derivedRestrict (f : Fin r → A) (E E' : derivedCat A)
    (hE : AlgebraicGeometry.RingedSpace.IsPerfect (X := (Spec A).toRingedSpace) E)
    (hE' : HasQuasicoherentCohomology A E')
    (α : (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).obj E ⟶
      (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).obj E') :
    ∃ (e : ℕ)
      (β : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E)
      (γ : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E'),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
          ((koszulDerivedSystem f).obj (op e)) ∧
        IsIso ((Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf
            (unionOfBasicOpens f)).map β) ∧
          (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map γ =
            (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map β ≫
              α :=
  Koszul.DerivedSystem.exists_roof_tensorKoszul f E E' hE hE' α

/-- **[Stacks, Tag 08EH] in the open-subspace model of restriction to `U`.** For `X = Spec A`,
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`, `E` perfect and `E'` with quasi-coherent cohomology, every map
`α : E|_U ⟶ E'|_U` fits into a roof `E ←β— Iₑ ⊗^𝐋 E —γ→ E'` with `Iₑ` a perfect stage of the
derived Koszul system on the powers of `f`, `β|_U` invertible and `γ|_U = β|_U ≫ α`.

`Koszul.DerivedSystem.exists_roof_tensorKoszul` is the same statement in the slice-site model;
`Stacks.DerivedQCoh.OpenLift.sliceRestrictCompIsoRestrictModules` and
`CategoryTheory.Functor.exists_roof_of_natIso_comp` carry it across. No tag attribute for
[Stacks, Tag 08EH] is placed here. -/
theorem exists_roof_restrictModules (f : Fin r → A) (E E' : derivedCat A)
    (hE : AlgebraicGeometry.RingedSpace.IsPerfect (X := (Spec A).toRingedSpace) E)
    (hE' : HasQuasicoherentCohomology A E')
    (α : (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).obj E ⟶
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).obj E') :
    ∃ (e : ℕ)
      (β : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E)
      (γ : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E'),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
          ((koszulDerivedSystem f).obj (op e)) ∧
        IsIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
            (unionOfBasicOpens f)).map β) ∧
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
              (unionOfBasicOpens f)).map γ =
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
              (unionOfBasicOpens f)).map β ≫ α := by
  let := isEquivalence_sliceToSubspace_mapDerivedCategory (unionOfBasicOpens f)
  -- The transport is instantiated first and applied afterwards: elaborating the roof of
  -- `exists_roof_derivedRestrict` as an argument of the same application exhausts the default
  -- heartbeat budget, while the two steps separately are immediate.
  have transport := CategoryTheory.Functor.exists_roof_of_natIso_comp _ _ _
    (sliceRestrictCompIsoRestrictModules (unionOfBasicOpens f))
    (fun e : ℕ => ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
      ((koszulDerivedSystem f).obj (op e))).obj E)
    (fun e : ℕ => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
      ((koszulDerivedSystem f).obj (op e))) E E'
  exact transport (fun α' => exists_roof_derivedRestrict f E E' hE hE' α') α

/-! ### Quasi-compact opens of an affine scheme -/

/-- **A quasi-compact open of `Spec A` is a finite union of basic opens.** This is what lets the
conclusion below be stated for an arbitrary quasi-compact open while
[Stacks, Tag 08EH] is consumed at `D(f₁) ∪ ⋯ ∪ D(f_r)`.

`PrimeSpectrum.isCompact_isOpen_iff` presents the open as the complement of the zero locus of a
finite set; indexing that set by `Finset.equivFin` turns it into the union of the basic opens of
`r` elements. The set-theoretic identity is proved once at the `Set (PrimeSpectrum A)` spelling
and crossed to `Set ↥(Spec A)` in term mode: the two are definitionally equal but `rw` matches at
`implicit` transparency and fails on the mixed goal. -/
theorem exists_unionOfBasicOpens_eq_of_isCompact (A : CommRingCat.{u}) (U : (Spec A).Opens)
    (hU : IsCompact ((U : (Spec A).Opens) : Set ↥(Spec A))) :
    ∃ (r : ℕ) (f : Fin r → A), unionOfBasicOpens f = U := by
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hU, U.isOpen⟩
  have key : (⋃ i : Fin t.card,
        (PrimeSpectrum.basicOpen ((t.equivFin.symm i : A)) : Set (PrimeSpectrum A))) =
      (PrimeSpectrum.zeroLocus (t : Set A))ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.not_subset]
      exact ⟨_, (t.equivFin.symm i).2, (PrimeSpectrum.mem_basicOpen _ x).mp hi⟩
    · intro hx
      rw [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hx
      obtain ⟨g, hgt, hgx⟩ := hx
      exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨g, hgt⟩,
        (PrimeSpectrum.mem_basicOpen _ x).mpr (by simpa using hgx)⟩
  exact ⟨t.card, fun i => (t.equivFin.symm i : A),
    Opens.ext ((Opens.coe_iSup _).trans (key.trans ht))⟩

/-! ### The conclusion -/

/-- **The cone step of the conclusion, at `U = D(f₁) ∪ ⋯ ∪ D(f_r)`.** Given a perfect `E` on
`X = Spec A` with `E|_U ≅ ℱ[n] ⊕ F`, and a roof `E ←β— Iₑ ⊗^𝐋 E —γ→ E` with `Iₑ` perfect,
`β|_U` invertible and `γ|_U = β|_U ≫ (x, y) ↦ (x, 0)`, the cone of `γ` is perfect and
restricts to `F ⊕ F[1]`.

The cone is perfect by [Stacks, Tag 08CR], its other two vertices being perfect — `Iₑ ⊗^𝐋 E` by
[Stacks, Tag 09J5] — and it restricts to `F ⊕ F[1]` by
`CategoryTheory.Limits.Biprod.nonempty_iso_biprod_shift_of_distTriang_idempotent`.

**Separated from the rest of the conclusion for the elaborator's budget.** Destructuring the roof
of `exists_roof_restrictModules` with this argument in the same declaration exhausts the default
heartbeat budget; with the roof's components as arguments it is immediate. -/
private theorem exists_isPerfect_biprod_shift_iso_restrict_of_roof (f : Fin r → A)
    (F : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding)))
    (E : derivedCat A)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) E)
    (L : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding)))
    (eU : L ⊞ F ≅ (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).obj E)
    (E₁ : derivedCat A)
    (hE₁ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) E₁)
    (β γ : E₁ ⟶ E)
    (hβ : IsIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).map β))
    (hγ : (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).map γ =
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).map β ≫ (eU.inv ≫ biprod.fst ≫ biprod.inl ≫ eU.hom)) :
    ∃ P : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P ∧
        Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
            (unionOfBasicOpens f)).obj P) := by
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle γ
  have hT' : (Triangle.mk γ v w : Triangle (DerivedCategory
        (StrictlyPerfect.OXMod.{u, u, u} (Spec A).toRingedSpace))) ∈ distTriang _ := hT
  -- Tag 08CR: the cone of `γ` is perfect.
  have hZ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) Z :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
      (X := (Spec A).toRingedSpace)
      (T := (Triangle.mk γ v w : Triangle (DerivedCategory
        (StrictlyPerfect.OXMod.{u, u, u} (Spec A).toRingedSpace)))) hT' hE₁ hE
  have hTU : (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).mapTriangle.obj (Triangle.mk γ v w : Triangle (DerivedCategory
        (StrictlyPerfect.OXMod.{u, u, u} (Spec A).toRingedSpace))) ∈
      distTriang (DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
        ((Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding))) :=
    AlgebraicGeometry.RingedSpace.map_distinguished_derivedRestrictModules
      (Spec A).toRingedSpace (unionOfBasicOpens f)
      (Triangle.mk γ v w : Triangle (DerivedCategory
        (StrictlyPerfect.OXMod.{u, u, u} (Spec A).toRingedSpace))) hT'
  refine ⟨Z, hZ, ?_⟩
  have := hβ
  obtain ⟨eZ⟩ := CategoryTheory.Limits.Biprod.nonempty_iso_biprod_shift_of_distTriang_idempotent
    eU.symm (asIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).map β)) (by exact hγ) hTU
  exact ⟨eZ.symm⟩

/-- **The roof step of the conclusion, at `U = D(f₁) ∪ ⋯ ∪ D(f_r)`.** Given a perfect `E` on
`X = Spec A` with `E|_U ≅ L ⊕ F`, `exists_roof_restrictModules` lifts the idempotent
`(x, y) ↦ (x, 0)` to a roof, whose middle object is perfect by [Stacks, Tag 09J5], and
`exists_isPerfect_biprod_shift_iso_restrict_of_roof` takes the cone.

The roof is taken apart by `Exists.elim` rather than by `obtain`: `rcases` eliminates
each component with the goal as motive, and that does not finish inside the default heartbeat
budget here (the same finding as the one recorded in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportedLiftStep.lean`). -/
private theorem exists_isPerfect_biprod_shift_iso_restrict_of_split (f : Fin r → A)
    (F : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding))) (E : derivedCat A)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) E)
    (hQC : HasQuasicoherentCohomology A E)
    (L : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding)))
    (eU : L ⊞ F ≅ (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).obj E) :
    ∃ P : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P ∧
        Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
            (unionOfBasicOpens f)).obj P) := by
  have hEr : AlgebraicGeometry.RingedSpace.IsPerfect (X := (Spec A).toRingedSpace) E := hE
  have roof := exists_roof_restrictModules f E E hEr hQC
    (eU.inv ≫ biprod.fst ≫ biprod.inl ≫ eU.hom)
  refine roof.elim fun e he => he.elim fun β hβ' => hβ'.elim fun γ h => ?_
  -- Tag 09J5: the middle object of the roof is perfect.
  have hE₁ := AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct (Spec A).toRingedSpace
    (AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite (affineSite A)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (affineSite A))) _ E h.1 hE
  exact exists_isPerfect_biprod_shift_iso_restrict_of_roof f F E hE L eU _ hE₁ β γ h.2.1 h.2.2

/-- **The conclusion at `U = D(f₁) ∪ ⋯ ∪ D(f_r)`.** [Stacks, Tag 08EG] gives the splitting and
`exists_isPerfect_biprod_shift_iso_restrict_of_split` does the rest. -/
private theorem exists_isPerfect_biprod_shift_iso_restrict_union (f : Fin r → A)
    (hU : IsCompact (((unionOfBasicOpens f : (Spec A).Opens)) : Set ↥(Spec A)))
    (F : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace.restrict (unionOfBasicOpens f).isOpenEmbedding) F) :
    ∃ P : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P ∧
        Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
            (unionOfBasicOpens f)).obj P) := by
  -- Tag 08EG: a perfect `E` on `X` with `E|_U ≅ ℱ[n] ⊕ F`.
  obtain ⟨n, G, P, -, hP, ⟨eU0⟩⟩ :=
    Stacks.DerivedQCoh.OpenLift.exists_finiteLocallyFree_biprod_iso_restrict_of_isPerfect
      (Spec A) (unionOfBasicOpens f) hU F hF
  have hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
      (DerivedCategory.Q.obj P) :=
    ⟨P, hP, ⟨Iso.refl _⟩⟩
  have hEr : AlgebraicGeometry.RingedSpace.IsPerfect (X := (Spec A).toRingedSpace)
      (DerivedCategory.Q.obj P) := hE
  exact exists_isPerfect_biprod_shift_iso_restrict_of_split f F _ hE
    (isQuasicoherentDerived_of_isPseudoCoherent (Spec A) _ hEr.isPseudoCoherent) _
    (eU0 ≪≫ ((AlgebraicGeometry.RingedSpace.restrictModules (Spec A).toRingedSpace
      (unionOfBasicOpens f)).mapDerivedCategoryFactors.app P).symm)

/-- **A perfect object of `D(𝒪_U)` plus its shift is the restriction of a perfect object of
`D(𝒪_X)`.** Let `X = Spec A` and let `U ⊆ X` be a quasi-compact open. For every perfect object
`F` of `D(𝒪_U)` there is a perfect object `P` of `D(𝒪_X)` with `F ⊕ F[1] ≅ P|_U`.

[Stacks, Tag 08EG] gives a perfect `E` on `X` with `E|_U ≅ ℱ[n] ⊕ F` for a finite locally free
`ℱ`; `Stacks.DerivedQCoh.OpenLift.exists_roof_restrictModules` lifts the idempotent
`(x, y) ↦ (x, 0)` of that splitting to a `γ : Iₑ ⊗^𝐋 E ⟶ E` restricting to it, up to the
invertible `β|_U`; the cone of `γ` is perfect by [Stacks, Tag 08CR] — its other two vertices are,
`Iₑ ⊗^𝐋 E` by [Stacks, Tag 09J5] — and restricts to `F ⊕ F[1]` by
`CategoryTheory.Limits.Biprod.nonempty_iso_biprod_shift_of_distTriang_idempotent`.

No tag attribute for [Stacks, Tag 08EI] is placed here. -/
theorem exists_isPerfect_biprod_shift_iso_restrict (U : (Spec A).Opens)
    (hU : IsCompact ((U : (Spec A).Opens) : Set ↥(Spec A)))
    (F : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace.restrict U.isOpenEmbedding) F) :
    ∃ P : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P ∧
        Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
            U).obj P) := by
  obtain ⟨r, f, rfl⟩ := exists_unionOfBasicOpens_eq_of_isCompact A U hU
  exact exists_isPerfect_biprod_shift_iso_restrict_union f hU F hF

end Stacks.DerivedQCoh.OpenLift

end
