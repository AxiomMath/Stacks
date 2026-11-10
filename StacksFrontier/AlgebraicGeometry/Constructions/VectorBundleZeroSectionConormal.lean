module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection
public import StacksFrontier.RingTheory.AugmentationIdealSymmetricAlgebra

/-!
# The conormal module of the zero section of `𝐕(ℰ)` on an affine chart

Let `X` be a scheme, `ℰ` a quasi-coherent `𝒪_X`-module, `𝐕(ℰ) = Spec_X(Sym(ℰ))` its vector
bundle and `V ⊆ X` an affine open.  The part of `𝐕(ℰ)` over `V` is affine, with sections the
symmetric algebra `Sym_{Γ(X, V)}(Γ(ℰ, V))`, and the zero section
`AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection` cuts out the augmentation ideal there.
This file proves that, and deduces that the conormal module of the zero section on the chart is
the cotangent module of the augmentation ideal, which
`SymmetricAlgebra.augmentationCotangentEquiv` identifies with `Γ(ℰ, V)`.

This is the local input of [Stacks, Tag 0B3V]: over an affine open of the base trivialising the
quotient line, the section of the projective bundle becomes the zero section of a vector bundle,
and its conormal sheaf is the kernel of the quotient.

## Main results

* `Stacks.SymAlgSections.symmetricAlgebraSheafAugmentation_app_symSectionsRingEquiv`: **the
  augmentation of `Sym(ℰ)` over an affine open is `SymmetricAlgebra.algebraMapInv`.**
* `Stacks.SymAlgSections.comap_ker_symmetricAlgebraSheafAugmentation_app`: hence its kernel is
  `SymmetricAlgebra.augmentationIdeal`, transported along
  `Stacks.SymAlgSections.symSectionsRingEquiv`;
  `Stacks.SymAlgSections.surjective_symmetricAlgebraSheafAugmentation_app` is its surjectivity.
* `Stacks.VectorBundleConormal.preimage_chartOpen`: the zero section meets the chart over `V` in
  `V` itself.
* `Stacks.VectorBundleConormal.appLE_vectorBundleZeroSection`: **the zero section of `𝐕(ℰ)` is
  cut out by the augmentation**, on the sections of the chart.
* `Stacks.VectorBundleConormal.comap_ker_appLE_vectorBundleZeroSection`: **the ideal of the zero
  section on the chart is the augmentation ideal.**
* `Stacks.VectorBundleConormal.zeroSectionCotangentIso`: **the conormal module `I/I²` of the zero
  section on the chart**, as a module over the chart's ring of sections.

## Main definitions

* `Stacks.VectorBundleConormal.chartSectionsIso` and
  `Stacks.VectorBundleConormal.chartSymSectionsIso`: the sections of `𝐕(ℰ)` over the chart above
  `V`, identified with the sections of `Sym(ℰ)` over `V` and with
  `Sym_{Γ(X, V)}(Γ(ℰ, V))`.

## Route

**The ring-level identification.**  Both the augmentation on sections and
`SymmetricAlgebra.algebraMapInv` are ring homomorphisms out of `Sym_{Γ(X, V)}(Γ(ℰ, V))`, so
`SymmetricAlgebra.induction` reduces their comparison to two generating cases.

* On the image of `algebraMap` it is the retraction property
  `AlgebraicGeometry.Scheme.Modules.hom_comp_symmetricAlgebraSheafAugmentation` paired with
  `Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap`, which says that the identification of
  the sections carries `algebraMap` to the structural ring map of the algebra sheaf.
* On a degree-one element it is the definition of the augmentation as the degree-zero component:
  `Stacks.SymAlgSections.symSectionsRingEquiv` sends `ι m` into the degree-one summand of the
  direct sum of the homogeneous pieces, and
  `Stacks.GradedAlgebra.degreeZeroComponent_incl_of_ne` kills it.  The passage from the
  sheafified realization to the presheaf of direct sums, where that computation lives, is
  `Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift`: the sheaf-level augmentation is the
  sheafification lift of the presheaf-level one.

**The geometric step.**  `AlgebraicGeometry.Scheme.Modules.ι_vectorBundleZeroSection` describes
the zero section over an affine open `V` of the base as the spectrum of the augmentation on
sections, read in the chart of `V`.  The chart is a monomorphism, so that description *is* the
restriction `AlgebraicGeometry.Scheme.Hom.resLE` of the zero section over the chart, and
`AlgebraicGeometry.Scheme.Hom.resLE_app_top` turns the restriction into the map on sections.
The two remaining comparisons are `AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop` and
`AlgebraicGeometry.Scheme.ΓSpecIso_naturality`.

**The conormal module.**  `Stacks.Conormal.cotangentComapIso` carries `Ideal.Cotangent` across
the identification of the chart's ring with `Sym_{Γ(X, V)}(Γ(ℰ, V))`, and
`SymmetricAlgebra.augmentationCotangentEquiv` evaluates the cotangent module of the augmentation
ideal as `Γ(ℰ, V)`.  No gluing is involved: the statements are about one chart.

**No hypothesis beyond the ambient ones.** `ℰ` is quasi-coherent and `V` affine, which is what
`Stacks.SymAlgSections.symSectionsRingEquiv` and `𝐕(ℰ)` already need; `ℰ` is not assumed finite
locally free, `Γ(ℰ, V)` is not assumed free or finitely generated, and `X` is an arbitrary
scheme.

**No tag.** The zero section of `𝐕(ℰ)` appears inside the proof of [Stacks, Tag 0B3V] and its
conormal module is not the assertion of a tag of its own; Tag 01M2 is the construction of
`𝐕(ℰ)` and carries no zero section.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped DirectSum

universe u

namespace Stacks.SymAlgSections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V)

omit [SheafOfModules.IsQuasicoherent E] in
/-- The sheaf-level augmentation of `Sym(ℰ)` on sections over an open is the presheaf-level
augmentation precomposed with the sheafification unit: the former is the sheafification lift of
the latter. -/
theorem symmetricAlgebraSheafAugmentation_app_totalUnit (W : (Opens X)ᵒᵖ)
    (z : (symPresheafAlgebra E).Total W) :
    ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app W).hom
        ((symPresheafAlgebra E).totalUnit (Opens.grothendieckTopology (X : TopCat)) W z) =
      ((Scheme.Modules.symmetricAlgebraTotalAugmentation X E).app W).hom z :=
  congrArg (fun φ => RingCat.Hom.hom φ z)
    (NatTrans.congr_app
      ((symPresheafAlgebra E).toTotalSheaf_totalSheafLift
        (Opens.grothendieckTopology (X : TopCat)) X.ringCatSheaf
        (Scheme.Modules.symmetricAlgebraTotalAugmentation X E)) W)

omit [SheafOfModules.IsQuasicoherent E] in
/-- The presheaf-level augmentation kills a homogeneous summand of nonzero degree. -/
theorem symmetricAlgebraTotalAugmentation_app_incl_of_ne {n : ℤ} (hn : n ≠ 0)
    (W : (Opens X)ᵒᵖ) (x : (symPiece E n).obj W) :
    ((Scheme.Modules.symmetricAlgebraTotalAugmentation X E).app W).hom
        ((symPresheafAlgebra E).incl n x) = 0 := by
  change Stacks.RelativeSpec.pieceZeroAugmentation (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebraPieceZeroIso X E) W
        ((symPresheafAlgebra E).degreeZeroComponent W ((symPresheafAlgebra E).incl n x)) = 0
  rw [(symPresheafAlgebra E).degreeZeroComponent_incl_of_ne hn W x, map_zero]

/-- The identification of the sections carries a degree-one element into the degree-one summand
of the direct sum of the homogeneous pieces of `Sym(ℰ)`. -/
theorem symSectionsRingEquiv_ι (m : Γ(E, V)) :
    symSectionsRingEquiv E hV (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m) =
      (symPresheafAlgebra E).totalUnit (Opens.grothendieckTopology (X : TopCat)) (op V)
        ((symPresheafAlgebra E).incl (1 : ℤ)
          (pieceUnit E hV 1 ⟨SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m,
            SymPow.ι_mem_symmetricPower _⟩)) := by
  have hdec : DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
      (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m) =
      DirectSum.of (fun k : ℕ => (SymPow.symmetricPower k Γ(X, V) Γ(E, V) : Type u)) 1
        ⟨SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m, SymPow.ι_mem_symmetricPower m⟩ :=
    DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
      (SymPow.ι_mem_symmetricPower m)
  change Stacks.RelativeSpec.totalSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) hV
        (ofSymPowers E hV (DirectSum.decompose
          (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
          (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m))) = _
  rw [hdec, ofSymPowers_of, symPowerIncl_apply]
  rfl

/-- The augmentation of `Sym(ℰ)` retracts the structure map of the algebra sheaf. -/
private theorem symmetricAlgebraSheafAugmentation_app_structure_map {X : Scheme.{u}}
    (E : X.Modules) (W : (Opens X)ᵒᵖ) (r : Γ(X, W.unop)) :
    ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app W).hom
        (((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app W).hom r) = r :=
  congrArg (fun φ => CommRingCat.Hom.hom φ r)
    (NatTrans.congr_app (Scheme.Modules.hom_comp_symmetricAlgebraSheafAugmentation X E) W)

/-- If `φ ∘ g` is `SymmetricAlgebra.algebraMapInv`, then the kernel of `φ` pulled back along `g`
is the augmentation ideal. -/
private theorem comap_ker_eq_augmentationIdeal {R M S : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [CommRing S] (φ : S →+* R) (g : SymmetricAlgebra R M →+* S)
    (h : ∀ x, φ (g x) = SymmetricAlgebra.algebraMapInv x) :
    (RingHom.ker φ).comap g = SymmetricAlgebra.augmentationIdeal R M :=
  Ideal.ext fun x => by
    rw [Ideal.mem_comap, RingHom.mem_ker, SymmetricAlgebra.mem_augmentationIdeal, h]

/-- **The augmentation of `Sym(ℰ)` over an affine open is `SymmetricAlgebra.algebraMapInv`.**
Under the identification `Stacks.SymAlgSections.symSectionsRingEquiv` of the sections of the
algebra sheaf `Sym(ℰ)` over an affine open `V` with the symmetric algebra of `Γ(ℰ, V)` over
`Γ(X, V)`, the morphism `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafAugmentation`
cutting out the zero section of `𝐕(ℰ)` is the ring-level augmentation. -/
theorem symmetricAlgebraSheafAugmentation_app_symSectionsRingEquiv
    (x : SymmetricAlgebra Γ(X, V) Γ(E, V)) :
    ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V)).hom
        (symSectionsRingEquiv E hV x) = SymmetricAlgebra.algebraMapInv x := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [symSectionsRingEquiv_algebraMap, SymmetricAlgebra.algebraMap_leftInverse]
      exact symmetricAlgebraSheafAugmentation_app_structure_map E (op V) r
  | ι m =>
      rw [symSectionsRingEquiv_ι, symmetricAlgebraSheafAugmentation_app_totalUnit,
        symmetricAlgebraTotalAugmentation_app_incl_of_ne E one_ne_zero,
        SymmetricAlgebra.algebraMapInv_ι]
      rfl
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

omit [SheafOfModules.IsQuasicoherent E] in
/-- **The augmentation of `Sym(ℰ)` is surjective on sections**, the structure map of the algebra
sheaf being a section of it. -/
theorem surjective_symmetricAlgebraSheafAugmentation_app (W : (Opens X)ᵒᵖ) :
    Function.Surjective
      ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app W).hom := fun r =>
  ⟨_, symmetricAlgebraSheafAugmentation_app_structure_map E W r⟩

/-- **The ideal cut out by the zero section of `𝐕(ℰ)` over an affine open is the augmentation
ideal.** The kernel of the augmentation on sections over `V`, pulled back along the
identification `Stacks.SymAlgSections.symSectionsRingEquiv` of those sections with
`Sym_{Γ(X, V)}(Γ(ℰ, V))`, is `SymmetricAlgebra.augmentationIdeal`. -/
theorem comap_ker_symmetricAlgebraSheafAugmentation_app :
    (RingHom.ker ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V)).hom).comap
        (symSectionsRingEquiv E hV).toRingHom =
      SymmetricAlgebra.augmentationIdeal Γ(X, V) Γ(E, V) := by
  exact comap_ker_eq_augmentationIdeal _ _
    (symmetricAlgebraSheafAugmentation_app_symSectionsRingEquiv E hV)

end Stacks.SymAlgSections

namespace Stacks.VectorBundleConormal

open AlgebraicGeometry.Scheme.Modules

section Chart

variable {X : Scheme.{u}} (E : SheafOfModules.{u} X.ringCatSheaf) [E.IsQuasicoherent]

/-- **The zero section meets the chart of `𝐕(ℰ)` over an open `V` of the base in `V` itself.**
The zero section splits the projection, so the preimage along it of the preimage of `V` is `V`. -/
theorem preimage_chartOpen (V : X.Opens) :
    vectorBundleZeroSection X E ⁻¹ᵁ (vectorBundleToBase X E ⁻¹ᵁ V) = V := by
  rw [← Scheme.Hom.comp_preimage, vectorBundleZeroSection_comp_vectorBundleToBase,
    Scheme.Hom.id_preimage]

variable (V : X.affineOpens)

/-- The chart of `𝐕(ℰ)` over an affine open `V` of the base, as an identification of the sections
of `𝐕(ℰ)` over the preimage of `V` with the sections of `Sym(ℰ)` over `V`. It is the inverse of
the universal map `Sym(ℰ) ⟶ π_* 𝒪_{𝐕(ℰ)}` of the relative spectrum on sections over `V`,
`Stacks.RelativeSpec.universalAlgebraMap`, which is invertible there by
`Stacks.RelativeSpec.isIso_universalAlgebraMap_app`. -/
def chartSectionsIso :
    Γ(vectorBundle X E, vectorBundleToBase X E ⁻¹ᵁ V.1) ≅
      (Scheme.Modules.symmetricAlgebraSheaf X E).sections V.1 :=
  haveI := Stacks.RelativeSpec.isIso_universalAlgebraMap_app (vectorBundleSituation X E) V
  (asIso ((Stacks.RelativeSpec.universalAlgebraMap (vectorBundleSituation X E)).right.app
    (op V.1))).symm

/-- **The zero section of `𝐕(ℰ)` is cut out by the augmentation of `Sym(ℰ)` over an affine open
of the base.**  Under the identification `Stacks.VectorBundleConormal.chartSectionsIso` of the
sections of `𝐕(ℰ)` over the chart with the sections of `Sym(ℰ)` over `V`, the map on sections
induced by the zero section is the augmentation
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafAugmentation`.

This is `AlgebraicGeometry.Scheme.Modules.ι_vectorBundleZeroSection` read on global sections.
The restriction of the zero section over the chart is the morphism of affine schemes that
statement names, because the chart is a monomorphism; the passage to rings is
`AlgebraicGeometry.Scheme.Hom.resLE_app_top` together with
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop` and
`AlgebraicGeometry.Scheme.ΓSpecIso_naturality`. -/
theorem appLE_vectorBundleZeroSection :
    (vectorBundleZeroSection X E).appLE (vectorBundleToBase X E ⁻¹ᵁ V.1) V.1
        (le_of_eq (preimage_chartOpen E V.1).symm) =
      (chartSectionsIso E V).hom ≫
        (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1) := by
  have hle : V.1 ≤ vectorBundleZeroSection X E ⁻¹ᵁ (vectorBundleToBase X E ⁻¹ᵁ V.1) :=
    le_of_eq (preimage_chartOpen E V.1).symm
  set W : (vectorBundle X E).Opens := vectorBundleToBase X E ⁻¹ᵁ V.1 with hW
  set a : X ⟶ vectorBundle X E := vectorBundleZeroSection X E with ha
  set R : CommRingCat.{u} := (Scheme.Modules.symmetricAlgebraSheaf X E).sections V.1 with hR
  set aug : R ⟶ Γ(X, V.1) :=
    (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1) with haug
  set G := Stacks.RelativeSpec.gluedSpectrum (vectorBundleSituation X E) with hG
  set c : Spec R ⟶ W.toScheme := (G.chartIsoPreimage V).hom with hc
  have hchart : c ≫ W.ι = G.chart V :=
    Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage_hom_ι G V
  set b : V.1.toScheme ⟶ W.toScheme := V.1.toSpecΓ ≫ Spec.map aug ≫ c with hb
  have hres : a.resLE W V.1 hle = b := by
    have : Mono W.ι := inferInstance
    rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, hb]
    simp only [Category.assoc]
    rw [hchart]
    exact ι_vectorBundleZeroSection X E V
  have htop : W.topIso.hom ≫ a.appLE W V.1 hle ≫ V.1.topIso.inv = b.appTop :=
    (Scheme.Hom.resLE_app_top a hle).symm.trans (congrArg Scheme.Hom.appTop hres)
  have hbtop : b.appTop = c.appTop ≫ (Spec.map aug).appTop ≫ V.1.toSpecΓ.appTop :=
    Category.assoc _ _ _
  have htail : (Spec.map aug).appTop ≫ V.1.toSpecΓ.appTop ≫ V.1.topIso.hom =
      (Scheme.ΓSpecIso R).hom ≫ aug := by
    rw [Scheme.Opens.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Scheme.ΓSpecIso_naturality]
  have hgoal : (chartSectionsIso E V).hom ≫ aug =
      W.topIso.inv ≫ c.appTop ≫ (Scheme.ΓSpecIso R).hom ≫ aug := by
    have := Stacks.RelativeSpec.isIso_universalAlgebraMap_app (vectorBundleSituation X E) V
    have hcc : (G.chartIsoPreimage V).inv.appTop ≫ (G.chartIsoPreimage V).hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    have hinv : (chartSectionsIso E V).hom = W.topIso.inv ≫ c.appTop ≫ (Scheme.ΓSpecIso R).hom := by
      rw [chartSectionsIso, Iso.symm_hom, asIso_inv]
      refine IsIso.inv_eq_of_hom_inv_id ?_
      refine (Category.assoc _ _ _).symm.trans ((congrArg
        (fun k => k ≫ c.appTop ≫ (Scheme.ΓSpecIso R).hom)
        (Stacks.RelativeSpec.universalAlgebraMap_app_comp_topIso_inv
          (vectorBundleSituation X E) V)).trans ?_)
      exact (Category.assoc _ _ _).trans
        ((congrArg ((Scheme.ΓSpecIso R).inv ≫ ·) ((reassoc_of% hcc) _)).trans (Iso.inv_hom_id _))
    rw [hinv]
    simp only [Category.assoc]
  calc a.appLE W V.1 hle
      = W.topIso.inv ≫ (W.topIso.hom ≫ a.appLE W V.1 hle ≫ V.1.topIso.inv) ≫
          V.1.topIso.hom := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    _ = W.topIso.inv ≫ b.appTop ≫ V.1.topIso.hom := by rw [htop]
    _ = W.topIso.inv ≫ (c.appTop ≫ (Spec.map aug).appTop ≫ V.1.toSpecΓ.appTop) ≫
          V.1.topIso.hom := by rw [hbtop]
    _ = W.topIso.inv ≫ c.appTop ≫ (Spec.map aug).appTop ≫ V.1.toSpecΓ.appTop ≫
          V.1.topIso.hom := by simp only [Category.assoc]
    _ = W.topIso.inv ≫ c.appTop ≫ (Scheme.ΓSpecIso R).hom ≫ aug := by rw [htail]
    _ = (chartSectionsIso E V).hom ≫
          (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1) := hgoal.symm

end Chart

section Conormal

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (V : X.affineOpens)

/-- The sections of `𝐕(ℰ)` over the chart above an affine open `V` of the base, as the symmetric
algebra of `Γ(ℰ, V)` over `Γ(X, V)`. -/
def chartSymSectionsIso :
    CommRingCat.of (SymmetricAlgebra Γ(X, V.1) Γ(E, V.1)) ≅
      Γ(vectorBundle X E, vectorBundleToBase X E ⁻¹ᵁ V.1) :=
  (Stacks.SymAlgSections.symSectionsRingEquiv E V.2).toCommRingCatIso ≪≫
    (chartSectionsIso E V).symm

/-- **The ideal cut out by the zero section of `𝐕(ℰ)` over the chart above an affine open of the
base is the augmentation ideal of the symmetric algebra.**

This is `Stacks.VectorBundleConormal.appLE_vectorBundleZeroSection` combined with
`Stacks.SymAlgSections.comap_ker_symmetricAlgebraSheafAugmentation_app`. -/
theorem comap_ker_appLE_vectorBundleZeroSection :
    (RingHom.ker ((vectorBundleZeroSection X E).appLE (vectorBundleToBase X E ⁻¹ᵁ V.1) V.1
        (le_of_eq (preimage_chartOpen E V.1).symm)).hom).comap
          (chartSymSectionsIso E V).hom.hom =
      SymmetricAlgebra.augmentationIdeal Γ(X, V.1) Γ(E, V.1) := by
  have hcomp : (chartSymSectionsIso E V).hom ≫ (chartSectionsIso E V).hom =
      (Stacks.SymAlgSections.symSectionsRingEquiv E V.2).toCommRingCatIso.hom := by
    change ((Stacks.SymAlgSections.symSectionsRingEquiv E V.2).toCommRingCatIso ≪≫
        (chartSectionsIso E V).symm).hom ≫ (chartSectionsIso E V).hom = _
    rw [Iso.trans_hom, Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
  refine Stacks.SymAlgSections.comap_ker_eq_augmentationIdeal _ _ fun x => ?_
  calc ((vectorBundleZeroSection X E).appLE (vectorBundleToBase X E ⁻¹ᵁ V.1) V.1
            (le_of_eq (preimage_chartOpen E V.1).symm)).hom
              ((chartSymSectionsIso E V).hom.hom x)
        = ((chartSymSectionsIso E V).hom ≫ (chartSectionsIso E V).hom ≫
            (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom x :=
          congrArg
            (fun φ : Γ(vectorBundle X E, vectorBundleToBase X E ⁻¹ᵁ V.1) ⟶ Γ(X, V.1) =>
              φ.hom ((chartSymSectionsIso E V).hom.hom x))
            (appLE_vectorBundleZeroSection E V)
      _ = (((chartSymSectionsIso E V).hom ≫ (chartSectionsIso E V).hom) ≫
            (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom x :=
          congrArg (fun φ : CommRingCat.of (SymmetricAlgebra Γ(X, V.1) Γ(E, V.1)) ⟶ Γ(X, V.1) =>
            φ.hom x) (Category.assoc _ _ _).symm
      _ = ((Stacks.SymAlgSections.symSectionsRingEquiv E V.2).toCommRingCatIso.hom ≫
            (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom x :=
          congrArg
            (fun φ : CommRingCat.of (SymmetricAlgebra Γ(X, V.1) Γ(E, V.1)) ⟶
                (Scheme.Modules.symmetricAlgebraSheaf X E).sections V.1 =>
              (φ ≫ (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom x)
            hcomp
      _ = ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom
            (Stacks.SymAlgSections.symSectionsRingEquiv E V.2 x) := rfl
      _ = SymmetricAlgebra.algebraMapInv x :=
          Stacks.SymAlgSections.symmetricAlgebraSheafAugmentation_app_symSectionsRingEquiv
            E V.2 x

/-- **The conormal module of the zero section of `𝐕(ℰ)` over the chart above an affine open of
the base.**  As a module over the sections `Sym_{Γ(X, V)}(Γ(ℰ, V))` of `Sym(ℰ)` on the chart, the
cotangent module `I/I²` of the ideal `I` that the zero section cuts out there is the cotangent
module of the augmentation ideal — which `SymmetricAlgebra.augmentationCotangentEquiv`
identifies with `Γ(ℰ, V)`.

`ℰ` is quasi-coherent and nothing more; it is not assumed finite locally free, and `X` is an
arbitrary scheme. -/
def zeroSectionCotangentIso :
    ModuleCat.of (SymmetricAlgebra Γ(X, V.1) Γ(E, V.1))
        (SymmetricAlgebra.augmentationIdeal Γ(X, V.1) Γ(E, V.1)).Cotangent ≅
      (ModuleCat.restrictScalars (chartSymSectionsIso E V).hom.hom).obj
        (ModuleCat.of Γ(vectorBundle X E, vectorBundleToBase X E ⁻¹ᵁ V.1)
          (RingHom.ker ((vectorBundleZeroSection X E).appLE
            (vectorBundleToBase X E ⁻¹ᵁ V.1) V.1
            (le_of_eq (preimage_chartOpen E V.1).symm)).hom).Cotangent) :=
  (Ideal.Cotangent.equivOfEq _ _
      (comap_ker_appLE_vectorBundleZeroSection E V).symm).toModuleIso ≪≫
    Stacks.Conormal.cotangentComapIso (chartSymSectionsIso E V) _

end Conormal

end Stacks.VectorBundleConormal

end
