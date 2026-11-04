module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite

/-!
# The reverse functor of formal glueing of quasi-coherent modules

In the formal glueing situation `f : Y ⟶ X`, `Z ⊆ X` of Stacks 0AEV, with `U = X ∖ Z`, with
`V = Y ∖ f⁻¹(Z)` and with `j : U ⟶ X`, `j' : V ⟶ Y` the two open immersions, a glueing triple
`(H, G, φ)` — a quasi-coherent `𝒪_U`-module, a quasi-coherent `𝒪_Y`-module and an isomorphism
`φ : (f|_V)^*H ≅ G|_V` — determines an `𝒪_X`-module

`Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))`,

the kernel of the difference of the two canonical maps: the one adjoint to `φ` on `j_*H`, and
the one adjoint to the identity on `f_*G`.  Its sections are the pairs of a section of `H` and a
section of `G` which agree on the overlap `V`.  This is the construction of Stacks 0AEX, going
in the direction opposite to the functor of Stacks 0AEW.

Both canonical maps are composites of a unit of the adjunction of Stacks 03LU with a direct-image
composition isomorphism of the same tag, and the first of them reads `φ` through the
commutativity `f ∘ j' = j ∘ f|_V` of the glueing square.  The kernel is formed in the category of
*all* `𝒪_X`-modules, where nothing has to be assumed; that it is quasi-coherent, so that the
construction is a functor into the quasi-coherent modules of Stacks 03G9, needs Stacks 03M9 for
the three morphisms `j`, `f` and `f ∘ j'`, Stacks 03GA for `j'`, and the kernel clause of
Stacks 03M1, none of which is available unconditionally in this development.  Those four inputs
are carried as named hypotheses; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.ModulePushforwardPreservesQuasicoherence`: Stacks 03M9 for a single
  morphism of algebraic spaces, as a property of it.
* `AlgebraicGeometry.Space.HasQuasicoherentKernels`: the kernel clause of Stacks 03M1 for a
  single algebraic space, as a property of it.
* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapImmersion`: the morphism
  `f ∘ j' : V ⟶ X` of the glueing square.
* `AlgebraicGeometry.Space.FormalGlueingSituation.restrictionDirectImage`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.ambientDirectImage` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.overlapDirectImage`: the three `𝒪_X`-modules
  `j_*H`, `f_*G` and `(f ∘ j')_*(G|_V)` attached to a glueing triple, as functors on the comma
  category of Stacks 0AEW.
* `AlgebraicGeometry.Space.FormalGlueingSituation.restrictionOverlapMap` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.ambientOverlapMap`: the two canonical maps to
  `(f ∘ j')_*(G|_V)`, and
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelMap`: **the map of Stacks 0AEX**,
  their difference on the direct sum.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelDiagram`: **the `𝒪_X`-module of
  Stacks 0AEX**, the kernel of that map, as a functor on the comma category.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelModules`: **the functor of
  Stacks 0AEX**, `QCoh(Y → X, Z) ⥤ QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapImmersion_eq`: the morphism
  `f ∘ j' : V ⟶ X` is also `j ∘ f|_V`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.restrictionDirectImage_obj`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.ambientDirectImage_obj` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.overlapDirectImage_obj`: the three functors
  take a triple `(H, G, φ)` to `j_*H`, to `f_*G` and to `(f ∘ j')_*(G|_V)`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.inl_comp_glueingKernelMap`: the map of
  Stacks 0AEX restricts to the first canonical map on the summand `j_*H`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelDiagramObjIso`: the value of the
  functor of Stacks 0AEX at a triple is the kernel of the map of Stacks 0AEX at that triple.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isQuasicoherentOnSite_glueingKernelDiagram_obj`:
  that kernel is quasi-coherent, granted the four inputs listed below; it is what makes the
  functor of Stacks 0AEX land in the quasi-coherent modules.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelModules_obj_obj` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelModules_map_hom`: the underlying
  `𝒪_X`-module and the underlying module map of the functor of Stacks 0AEX are the kernel and the
  induced map on kernels, which pins that functor down.

## Implementation notes

**The construction is a functor because it is a kernel in a functor category.**  The two
canonical maps are natural transformations `restrictionDirectImage ⟶ overlapDirectImage` and
`ambientDirectImage ⟶ overlapDirectImage` of functors on the comma category of Stacks 0AEW; the
direct sum, the difference and the kernel are then formed in the abelian category of functors
from that comma category to the `𝒪_X`-modules, so the functoriality of the construction is the
functoriality of a kernel and no functor law is proved at the concrete categories of modules.
This is the discipline that
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/FormalGlueingModulesFunctor.lean` records for
Stacks 0AEW, for the same reason: an identity between morphisms of sheaves of modules on the
small étale site of `V`, whose structure sheaf takes the proof that `V` is an algebraic space as
an argument, is out of reach of the elaborator and of the kernel.  For the same reason the
morphism `f ∘ j'` is a definition and not an abbreviation.  The value of the resulting functor at
a triple is identified with the kernel of the value of the map by
`AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelDiagramObjIso`, which is the
statement that evaluation preserves kernels.

`AlgebraicGeometry.Space.FormalGlueingSituation.restrictionOverlapMap` is `j_*` of the unit
`H ⟶ (f|_V)_*(f|_V)^*H` of the adjunction of Stacks 03LU, followed by the direct-image
composition isomorphism `(f|_V)_* ∘ j_* ≅ (j ∘ f|_V)_*` of the same tag, then by `(j ∘ f|_V)_*`
of the structure arrow `φ` of the triple — which is
`CategoryTheory.Comma.natTrans` — and finally by the transport along the commutativity
`j ∘ f|_V = f ∘ j'` of the glueing square.
`AlgebraicGeometry.Space.FormalGlueingSituation.ambientOverlapMap` is the same without the last
two steps: `f_*` of the unit `G ⟶ j'_*(j')^*G`, followed by `j'_* ∘ f_* ≅ (f ∘ j')_*`.  Their
difference is taken because the kernel is to consist of the pairs of sections *agreeing* on the
overlap; the source displays only the arrow.  Only the first of the two components of the map is
recorded as a lemma: the companion statement
`biprod.inr ≫ glueingKernelMap = -ambientOverlapMap` is an instance of
`CategoryTheory.Limits.biprod.inr_desc`, and reducing a biproduct identity whose right-hand side
is an additive inverse at these types exhausts the kernel; the definition itself is exposed, so
nothing about the map is hidden by its absence.

**The four hypotheses are quasi-coherence inputs of Chapter 0GNB and say nothing about formal
glueing.**  Each is stated in the shape in which the corresponding reduction already present in
the tree delivers its conclusion, so that the day its tag lands each discharges by a single
application and nothing in this file changes.

* `AlgebraicGeometry.Space.ModulePushforwardPreservesQuasicoherence` for `j`, for `f` and for
  `f ∘ j'` is **Stacks 03M9**, quasi-coherence of a direct image.  Stacks 03M9 is not in the
  tree: `StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardReduction.lean` carries the
  reduction `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine`, whose
  hypothesis `haffine` is the whole second step of the Stacks argument, and the affine case
  itself is the unproved predicate
  `AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDirectImageAffine.lean`.  All three
  morphisms need it; no form of it for open immersions, for étale morphisms or for closed
  immersions is available either.  The predicate here is stated for
  `AlgebraicGeometry.Space.modulePushforward`, the direct image read with `𝒪`-coefficients, which
  is the functor Stacks 03M9 is about and the conclusion shape of that reduction; the existing
  `DirectImagePreservesQuasicoherence` is the different statement about
  `AlgebraicGeometry.Space.moduleDirectImage`, with coefficients in `f_*𝒪`.
* `AlgebraicGeometry.Space.HasQuasicoherentKernels` for `X` is the kernel clause of
  **Stacks 03M1**.  Every form of it in
  `StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentKernelsOnSite.lean` is conditional:
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel` on a local presentation step, and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` — against whose
  conclusion the predicate here is shaped — on Descent, Proposition 03DX(2) for the small étale
  site.
* `AlgebraicGeometry.Space.HasLocalInverseImagePresentations` for `j'` is **Stacks 03GA**,
  quasi-coherence of a pullback, in the form
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean` provides:
  that file carries Stacks 03GA as
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback`, conditional on this predicate,
  the one clause of Stacks 03DO it does not prove.  It enters because the module pushed forward
  along `f ∘ j'` is the restriction `G|_V`, and Stacks 03M9 asks for a quasi-coherent source.
  The functor of Stacks 0AEW carries the same predicate for `j` and for `f`.

The direct sum needs nothing: quasi-coherence is closed under binary biproducts
unconditionally, by `SheafOfModules.isQuasicoherentOnSite_biprod`.  No hypothesis of the formal
glueing situation is used beyond the openness of `U` and of `V`, exactly as for Stacks 0AEW; in
particular neither the finite presentation of `Z` nor the flatness of `f` along `f⁻¹(Z)` enters,
and they are not needed until the two functors are compared.

The module universe is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePullback` exists only there; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`.

## References

* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03M9 for a single morphism of algebraic spaces**, as a property of it: the direct
image along `f` of every quasi-coherent `𝒪_X`-module is a quasi-coherent `𝒪_Y`-module.

The direct image is `AlgebraicGeometry.Space.modulePushforward`, the one of Stacks 03LU with
`𝒪`-coefficients; the variant with coefficients in `f_*𝒪_X` is
`AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence`. -/
def ModulePushforwardPreservesQuasicoherence {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite

/-- **The kernel clause of Stacks 03M1 for a single algebraic space**, as a property of it: the
kernel of a morphism of quasi-coherent `𝒪_F`-modules on the small étale site of `F` is
quasi-coherent. -/
def HasQuasicoherentKernels (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : Prop :=
  ∀ {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N), M.IsQuasicoherentOnSite →
    N.IsQuasicoherentOnSite → (kernel φ).IsQuasicoherentOnSite

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-! ### The three direct images attached to a glueing triple -/

/-- The comma category of the two pullbacks to the overlap `V`, whose objects are the triples
`(H, G, φ)` with `φ` an arbitrary `𝒪_V`-module map; the glueing data of Stacks 0AEW is the full
subcategory `AlgebraicGeometry.Space.FormalGlueingSituation.moduleGlueingData` of it. -/
abbrev moduleGlueingComma :=
  Comma (modulePullback B S hS D.overlapRestriction)
    (modulePullback B S hS D.openImmersionOver)

/-- The morphism `f ∘ j' : V ⟶ X` of the glueing square: the open immersion of the complement of
`f⁻¹(Z)` followed by the morphism being glued along. -/
def overlapImmersion : D.spaceV ⟶ D.spaceX :=
  D.openImmersionOver ≫ D.ambientMorphism

/-- The two legs of the glueing square agree: `f ∘ j'` is also `j ∘ f|_V`. -/
theorem overlapImmersion_eq :
    D.overlapImmersion = D.overlapRestriction ≫ D.openImmersion :=
  D.overlapRestriction_comp_openImmersion.symm

/-- The direct image `j_*H` to `X` of the `𝒪_U`-module component of a glueing triple. -/
def restrictionDirectImage :
    D.moduleGlueingComma ⥤ Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  Comma.fst _ _ ⋙ modulePushforward B S hS D.openImmersion

/-- The direct image `f_*G` to `X` of the `𝒪_Y`-module component of a glueing triple. -/
def ambientDirectImage :
    D.moduleGlueingComma ⥤ Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  Comma.snd _ _ ⋙ modulePushforward B S hS D.ambientMorphism

/-- The direct image `(f ∘ j')_*(G|_V)` to `X` of the restriction to the overlap of the
`𝒪_Y`-module component of a glueing triple. -/
def overlapDirectImage :
    D.moduleGlueingComma ⥤ Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  (Comma.snd _ _ ⋙ modulePullback B S hS D.openImmersionOver) ⋙
    modulePushforward B S hS D.overlapImmersion

/-- The value of `restrictionDirectImage` at a glueing triple `(H, G, φ)` is `j_*H`. -/
@[simp]
theorem restrictionDirectImage_obj (t : D.moduleGlueingComma) :
    D.restrictionDirectImage.obj t = (modulePushforward B S hS D.openImmersion).obj t.left :=
  rfl

/-- The value of `ambientDirectImage` at a glueing triple `(H, G, φ)` is `f_*G`. -/
@[simp]
theorem ambientDirectImage_obj (t : D.moduleGlueingComma) :
    D.ambientDirectImage.obj t = (modulePushforward B S hS D.ambientMorphism).obj t.right :=
  rfl

/-- The value of `overlapDirectImage` at a glueing triple `(H, G, φ)` is `(f ∘ j')_*(G|_V)`. -/
@[simp]
theorem overlapDirectImage_obj (t : D.moduleGlueingComma) :
    D.overlapDirectImage.obj t = (modulePushforward B S hS D.overlapImmersion).obj
      ((modulePullback B S hS D.openImmersionOver).obj t.right) :=
  rfl

/-! ### The map of Stacks 0AEX and its kernel -/

/-- The canonical map `j_*H ⟶ (f ∘ j')_*(G|_V)`: the direct image along `j` of the unit
`H ⟶ (f|_V)_*(f|_V)^*H` of Stacks 03LU, composed with the direct-image composition isomorphism
of that tag, with the structure arrow `φ : (f|_V)^*H ⟶ G|_V` of the triple pushed forward, and
with the transport along the commutativity of the glueing square. -/
def restrictionOverlapMap : D.restrictionDirectImage ⟶ D.overlapDirectImage :=
  Functor.whiskerRight (Functor.whiskerLeft (Comma.fst _ _)
      (modulePullbackAdjunction B S hS D.overlapRestriction).unit)
      (modulePushforward B S hS D.openImmersion) ≫
    Functor.whiskerLeft (Comma.fst _ _ ⋙ modulePullback B S hS D.overlapRestriction)
      (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion).hom ≫
    Functor.whiskerRight (Comma.natTrans _ _)
      (modulePushforward B S hS (D.overlapRestriction ≫ D.openImmersion)) ≫
    Functor.whiskerLeft (Comma.snd _ _ ⋙ modulePullback B S hS D.openImmersionOver)
      (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
        D.overlapRestriction_comp_openImmersion))

/-- The canonical map `f_*G ⟶ (f ∘ j')_*(G|_V)`: the direct image along `f` of the unit
`G ⟶ j'_*(j')^*G` of Stacks 03LU, composed with the direct-image composition isomorphism of that
tag. -/
def ambientOverlapMap : D.ambientDirectImage ⟶ D.overlapDirectImage :=
  Functor.whiskerRight (Functor.whiskerLeft (Comma.snd _ _)
      (modulePullbackAdjunction B S hS D.openImmersionOver).unit)
      (modulePushforward B S hS D.ambientMorphism) ≫
    Functor.whiskerLeft (Comma.snd _ _ ⋙ modulePullback B S hS D.openImmersionOver)
      (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism).hom

/-- **The map `j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V)` of Stacks 0AEX**: the difference of the two
canonical maps to the direct image from the overlap, so that a pair of sections lies in its
kernel exactly when the two sections agree on the overlap. -/
@[stacks 0AEX "the map out of the direct sum"]
def glueingKernelMap :
    D.restrictionDirectImage ⊞ D.ambientDirectImage ⟶ D.overlapDirectImage :=
  biprod.desc D.restrictionOverlapMap (-D.ambientOverlapMap)

/-- The restriction of `glueingKernelMap` to the summand `j_*H` is `restrictionOverlapMap`. -/
@[simp]
theorem inl_comp_glueingKernelMap :
    biprod.inl ≫ D.glueingKernelMap = D.restrictionOverlapMap :=
  biprod.inl_desc _ _

/-- **The `𝒪_X`-module `Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))` of Stacks 0AEX**, as a functor of
the glueing triple.  It is the kernel in the category of functors to the `𝒪_X`-modules, so no
quasi-coherence is assumed and the functoriality is that of a kernel. -/
@[stacks 0AEX "the kernel module, as a functor of the glueing triple"]
def glueingKernelDiagram :
    D.moduleGlueingComma ⥤ Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  kernel D.glueingKernelMap

/-- The value at a glueing triple of the module of Stacks 0AEX is the kernel of the value of the
map of Stacks 0AEX: evaluation at an object preserves kernels. -/
def glueingKernelDiagramObjIso (t : D.moduleGlueingComma) :
    D.glueingKernelDiagram.obj t ≅ kernel (D.glueingKernelMap.app t) :=
  PreservesKernel.iso ((evaluation _ _).obj t) D.glueingKernelMap

/-- The value at a glueing triple of the direct sum `j_*H ⊕ f_*G`, formed in the category of
functors, is the direct sum of the two values: evaluation at an object is additive. -/
def directImageSumObjIso (t : D.moduleGlueingComma) :
    (D.restrictionDirectImage ⊞ D.ambientDirectImage).obj t ≅
      D.restrictionDirectImage.obj t ⊞ D.ambientDirectImage.obj t :=
  have := preservesBinaryBiproducts_of_preservesBiproducts
    ((evaluation D.moduleGlueingComma (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)).obj t)
  ((evaluation _ _).obj t).mapBiprod _ _

/-! ### Quasi-coherence and the functor of Stacks 0AEX -/

/-- **Stacks 03M9 for `j`.**  The direct image `j_*H` of the quasi-coherent `𝒪_U`-module
component of a glueing triple is quasi-coherent. -/
theorem isQuasicoherentOnSite_restrictionDirectImage_obj
    (quasicoherentPushforward_openImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion)
    (t : D.moduleGlueingComma) (ht : t.left.IsQuasicoherentOnSite) :
    (D.restrictionDirectImage.obj t).IsQuasicoherentOnSite :=
  quasicoherentPushforward_openImmersion t.left ht

/-- **Stacks 03M9 for `f`.**  The direct image `f_*G` of the quasi-coherent `𝒪_Y`-module
component of a glueing triple is quasi-coherent. -/
theorem isQuasicoherentOnSite_ambientDirectImage_obj
    (quasicoherentPushforward_ambientMorphism :
      ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism)
    (t : D.moduleGlueingComma) (ht : t.right.IsQuasicoherentOnSite) :
    (D.ambientDirectImage.obj t).IsQuasicoherentOnSite :=
  quasicoherentPushforward_ambientMorphism t.right ht

/-- **Stacks 03M9 for `f ∘ j'`, on a source supplied by Stacks 03GA for `j'`.**  The direct image
`(f ∘ j')_*(G|_V)` of the restriction to the overlap of the quasi-coherent `𝒪_Y`-module component
of a glueing triple is quasi-coherent. -/
theorem isQuasicoherentOnSite_overlapDirectImage_obj
    (quasicoherentPushforward_overlapImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.overlapImmersion)
    (quasicoherentPullback_openImmersionOver :
      HasLocalInverseImagePresentations B S hS D.openImmersionOver)
    (t : D.moduleGlueingComma) (ht : t.right.IsQuasicoherentOnSite) :
    (D.overlapDirectImage.obj t).IsQuasicoherentOnSite :=
  quasicoherentPushforward_overlapImmersion _
    (isQuasicoherentOnSite_modulePullback B S hS D.openImmersionOver
      quasicoherentPullback_openImmersionOver t.right ht)

/-- The direct sum `j_*H ⊕ f_*G` of a glueing triple is quasi-coherent: quasi-coherence is
closed under binary biproducts unconditionally, so this needs only Stacks 03M9 for `j` and
for `f`. -/
theorem isQuasicoherentOnSite_directImageSum_obj
    (quasicoherentPushforward_openImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion)
    (quasicoherentPushforward_ambientMorphism :
      ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism)
    (t : D.moduleGlueingComma) (hleft : t.left.IsQuasicoherentOnSite)
    (hright : t.right.IsQuasicoherentOnSite) :
    ((D.restrictionDirectImage ⊞ D.ambientDirectImage).obj t).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (D.directImageSumObjIso t).symm
    (SheafOfModules.isQuasicoherentOnSite_biprod
      (D.isQuasicoherentOnSite_restrictionDirectImage_obj
        quasicoherentPushforward_openImmersion t hleft)
      (D.isQuasicoherentOnSite_ambientDirectImage_obj
        quasicoherentPushforward_ambientMorphism t hright))

/-- **The module of Stacks 0AEX attached to a glueing triple is quasi-coherent**, granted
Stacks 03M9 for the three morphisms `j`, `f` and `f ∘ j'` of the glueing square, Stacks 03GA for
`j'`, and the kernel clause of Stacks 03M1 for `X`. -/
theorem isQuasicoherentOnSite_glueingKernelDiagram_obj
    (quasicoherentPushforward_openImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion)
    (quasicoherentPushforward_ambientMorphism :
      ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism)
    (quasicoherentPushforward_overlapImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.overlapImmersion)
    (quasicoherentPullback_openImmersionOver :
      HasLocalInverseImagePresentations B S hS D.openImmersionOver)
    (quasicoherentKernels : HasQuasicoherentKernels B S hS D.spaceX.1 D.spaceX.2)
    (t : D.moduleGlueingComma) (hleft : t.left.IsQuasicoherentOnSite)
    (hright : t.right.IsQuasicoherentOnSite) :
    (D.glueingKernelDiagram.obj t).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (D.glueingKernelDiagramObjIso t).symm
    (quasicoherentKernels (D.glueingKernelMap.app t)
      (D.isQuasicoherentOnSite_directImageSum_obj quasicoherentPushforward_openImmersion
        quasicoherentPushforward_ambientMorphism t hleft hright)
      (D.isQuasicoherentOnSite_overlapDirectImage_obj
        quasicoherentPushforward_overlapImmersion quasicoherentPullback_openImmersionOver
        t hright))

/-- **Stacks 0AEX.**  The functor `QCoh(Y → X, Z) ⥤ QCoh(𝒪_X)` in the direction opposite to
Stacks 0AEW: a glueing triple `(H, G, φ)` goes to the quasi-coherent `𝒪_X`-module
`Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))`.

The five hypotheses are Stacks 03M9 for `j`, for `f` and for `f ∘ j'`, Stacks 03GA for `j'`, and
the kernel clause of Stacks 03M1 for `X`; see the implementation notes. -/
def glueingKernelModules
    (quasicoherentPushforward_openImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion)
    (quasicoherentPushforward_ambientMorphism :
      ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism)
    (quasicoherentPushforward_overlapImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.overlapImmersion)
    (quasicoherentPullback_openImmersionOver :
      HasLocalInverseImagePresentations B S hS D.openImmersionOver)
    (quasicoherentKernels : HasQuasicoherentKernels B S hS D.spaceX.1 D.spaceX.2) :
    D.moduleGlueingData ⥤ QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ D.glueingKernelDiagram) fun t ↦
    D.isQuasicoherentOnSite_glueingKernelDiagram_obj quasicoherentPushforward_openImmersion
      quasicoherentPushforward_ambientMorphism quasicoherentPushforward_overlapImmersion
      quasicoherentPullback_openImmersionOver quasicoherentKernels t.obj
      t.property.2.1 t.property.2.2

variable (quasicoherentPushforward_openImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion)
    (quasicoherentPushforward_ambientMorphism :
      ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism)
    (quasicoherentPushforward_overlapImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.overlapImmersion)
    (quasicoherentPullback_openImmersionOver :
      HasLocalInverseImagePresentations B S hS D.openImmersionOver)
    (quasicoherentKernels : HasQuasicoherentKernels B S hS D.spaceX.1 D.spaceX.2)

/-- The underlying `𝒪_X`-module of the value of `glueingKernelModules` at a glueing triple is the
value of `glueingKernelDiagram` at that triple. -/
@[simp]
theorem glueingKernelModules_obj_obj (t : D.moduleGlueingData) :
    ((D.glueingKernelModules quasicoherentPushforward_openImmersion
        quasicoherentPushforward_ambientMorphism quasicoherentPushforward_overlapImmersion
        quasicoherentPullback_openImmersionOver quasicoherentKernels).obj t).obj =
      D.glueingKernelDiagram.obj t.obj :=
  rfl

/-- The underlying `𝒪_X`-module map of the image under `glueingKernelModules` of a morphism of
glueing triples is its image under `glueingKernelDiagram`. -/
@[simp]
theorem glueingKernelModules_map_hom {t s : D.moduleGlueingData} (a : t ⟶ s) :
    InducedCategory.Hom.hom ((D.glueingKernelModules quasicoherentPushforward_openImmersion
        quasicoherentPushforward_ambientMorphism quasicoherentPushforward_overlapImmersion
        quasicoherentPullback_openImmersionOver quasicoherentKernels).map a) =
      D.glueingKernelDiagram.map (InducedCategory.Hom.hom a) :=
  rfl

end AlgebraicGeometry.Space.FormalGlueingSituation

end
