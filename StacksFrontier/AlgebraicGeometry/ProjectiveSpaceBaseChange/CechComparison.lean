module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechDegreewise
public import StacksFrontier.CategoryTheory.Sites.CechComplexComparison
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# The Čech complex of a cover under base change

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, let `F` be a quasi-coherent
`𝒪_X`-module and let `U : ι → X.Opens` be a finite cover of `X` all of whose nonempty finite
intersections are affine. This file identifies the Čech complex of the preimage cover of
`p^* F` with the base change of the Čech complex of `U` and `F`:

  `Č(p⁻¹U, p^* F) ≅ Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Č(U, F)`

as cochain complexes of `Γ(T, ⊤)`-modules, and specialises that to the standard charts of
projective space. It is the sentence *"we have the following relation between the Čech
complexes"* in the proof of [Stacks, Tag 02KH] part (2), at the level of complexes rather than
degreewise.

No flatness is used. Flatness of `q` enters only when homology is taken; what is proved here is
an isomorphism of complexes, for which additivity of the two change-of-rings functors is all
that is needed.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionsBaseChange.baseRestrictScalars` and
  `baseExtendScalars`: the two change-of-rings functors on global sections of the structure
  sheaves, whose composite is `- ↦ Γ(T, ⊤) ⊗_{Γ(S, ⊤)} -` read on a `Γ(X, ⊤)`-module.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.rescaleSource` and `rescaleTarget`: the two
  identity-on-carriers rescalings reconciling the Čech coefficient module with the scalar
  structure the degreewise comparison is stated for.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.degreewiseIso`: the degreewise comparison
  packaged as an isomorphism of `Γ(T, ⊤)`-modules.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.comparisonDeg`: the comparison at one nonempty
  tuple of members of the cover, in the shape the generic assembly consumes.

## Main results

* `Stacks.AlgebraicGeometry.SectionsBaseChange.flat_appLE_Spec_map` and
  `preservesHomology_baseChange`: over affine bases the change-of-rings functor is exact as soon
  as the ring map is flat — the step at which flatness enters, a layer after the comparison.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.comparisonDeg_comm`: **the comparisons commute
  with the reindexing maps**, hence with the Čech differentials.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.cechBaseChangeIso` and
  `cechBaseChangeIsoOfPreimage`: **the isomorphism of Čech cochain complexes.**
* `Stacks.ProjectiveCohomology.cechBaseChangeIsoChart`: the same for the `n + 1` standard
  charts of projective `n`-space over a ring.

## Implementation notes

**The scalar structures and why two rescalings are needed.** The coefficient object of the Čech
complex of [Stacks, Tag 01EP] over an open `W` of `X` is the sections `Γ(F, W)` as a module over
`Γ(X, ⊤)`, i.e. the native `Γ(X, W)`-module restricted along `Γ(X, ⊤) ⟶ Γ(X, W)`. Restricting
that further along `iX` on global sections composes a *second* `Module.compHom`, whereas the
degreewise comparison
`Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap` is stated for
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`, which is *one* `Module.compHom`, along
`iX.appLE ⊤ W`. The two actions agree pointwise — that is
`AlgebraicGeometry.Scheme.Hom.appLE_map` — but the instances are not definitionally equal, so the
two tensor products are different types and the degreewise map cannot be used directly. The
reconciliation is Mathlib's `ModuleCat.restrictScalarsComp'App`, whose components are the
identity on carriers, applied with exactly that equation; on the source side it is then pushed
through `ModuleCat.extendScalars`. Both rescalings are identity on elements by `rfl`, which is
why `comparisonDeg_hom_tmul` holds by `rfl` and the compatibility reduces to one application of
`pullbackUnitSections_naturality`.

**Only nonempty tuples.** The generic assembly asks for the comparison at tuples
`Fin (m + 1) → ι` only. That restriction is essential here and not a convenience: the comparison
at the empty tuple would be base change on the sections over the whole of `X`, which is the
*conclusion* of the argument, and the affineness hypothesis that makes the degreewise comparison
an isomorphism is available precisely for nonempty intersections.

**The cover upstairs.** It is the preimage cover, which covers `Y` because the preimage of `⊤`
is `⊤` — no surjectivity of `p` is needed. `cechBaseChangeIsoOfPreimage` takes the second cover
as a parameter together with a memberwise identification with the preimage cover, so that a
consumer whose second cover is *equal but not syntactically* the preimage cover — the standard
charts of projective space, by
`Stacks.ProjectiveCohomology.preimage_chartAtUniverse` — can use it without transporting
anything: the two covering hypotheses are propositions and so are identified by proof
irrelevance once the covers are.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf cechComplex
  inter_coverObject_left)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.SectionsBaseChange

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}

/-! ### The two change-of-rings functors -/

/-- Restriction of scalars from `Γ(X, ⊤)` to `Γ(S, ⊤)` along a morphism `iX : X ⟶ S`. -/
public abbrev baseRestrictScalars (iX : X ⟶ S) :
    ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  ModuleCat.restrictScalars (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom

/-- Extension of scalars from `Γ(S, ⊤)` to `Γ(T, ⊤)` along a morphism `q : T ⟶ S`. -/
public abbrev baseExtendScalars (q : T ⟶ S) :
    ModuleCat.{u} Γ(S, ⊤) ⥤ ModuleCat.{u} Γ(T, ⊤) :=
  ModuleCat.extendScalars (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom

/-- **Over affine bases the extension of scalars is the ring map itself**, as far as flatness is
concerned: `(Spec.map φ).appLE ⊤ ⊤` is `φ` conjugated by the two units of the `Γ`–`Spec`
adjunction, so it is flat as soon as `φ` is. This is what makes the homology step of the Čech
comparison over an affine base cost nothing beyond flatness of the ring map. -/
public theorem flat_appLE_Spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : RingHom.Flat φ.hom) :
    RingHom.Flat ((Spec.map φ).appLE ⊤ ⊤ (le_preimage_top (Spec.map φ) ⊤)).hom := by
  rw [(Spec.map φ).appLE_congr (le_preimage_top (Spec.map φ) ⊤) rfl
    ((Spec.map φ).preimage_top).symm (fun g => RingHom.Flat g.hom),
    Scheme.Hom.appLE_eq_app]
  have h1 : (Spec.map φ).app (⊤ : (Spec A).Opens)
      = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hiso : ∀ {C D : CommRingCat.{u}} (e : C ⟶ D) [IsIso e], RingHom.Flat e.hom := fun e =>
    RingHom.Flat.of_bijective ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)
  rw [h1]
  exact ((hiso (Scheme.ΓSpecIso A).hom).comp hφ).comp (hiso (Scheme.ΓSpecIso B).inv)

/-- **The change-of-rings functor the comparison uses preserves homology when the base ring map
is flat.** Restriction of scalars has both adjoints, so it is exact unconditionally; extension
of scalars is right exact unconditionally and left exact under flatness
(`extendScalars_preservesFiniteLimits_of_flat'`). This is the step at which flatness
enters: the isomorphism of Čech complexes below needs none. -/
public theorem preservesHomology_baseChange (iX : X ⟶ S) (q : T ⟶ S)
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom) :
    (baseRestrictScalars iX ⋙ baseExtendScalars q).PreservesHomology := by
  have h1 : Limits.PreservesFiniteLimits (baseExtendScalars q) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hq
  have : Limits.PreservesFiniteLimits (baseRestrictScalars iX ⋙ baseExtendScalars q) :=
    inferInstance
  have : Limits.PreservesFiniteColimits (baseRestrictScalars iX ⋙ baseExtendScalars q) :=
    inferInstance
  exact Functor.preservesHomologyOfExact _

/-! ### Reconciling the two scalar structures -/

/-- **The rescaling downstairs.** The Čech coefficient module over an open `Z.left` of `X`,
restricted along `iX` on global sections, carries the same `Γ(S, ⊤)`-action as
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`; this is the identity-on-carriers
isomorphism between the two, from `AlgebraicGeometry.Scheme.Hom.appLE_map`. -/
public def rescaleSource (iX : X ⟶ S) (F : X.Modules) (Z : Over (⊤ : X.Opens)) :
    letI := baseModule iX F Z.left
    (baseRestrictScalars iX).obj ((sectionsPresheaf (⊤ : X.Opens) F).obj (op Z)) ≅
      ModuleCat.of Γ(S, ⊤) Γ(F, Z.left) :=
  letI := baseModule iX F Z.left
  (ModuleCat.restrictScalarsComp'App
    (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom
    (X.presheaf.map (homOfLE (leOfHom Z.hom)).op).hom
    (iX.appLE ⊤ Z.left (le_preimage_top iX Z.left)).hom
    (by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom
        (Scheme.Hom.appLE_map iX (le_preimage_top iX ⊤) (homOfLE (leOfHom Z.hom)).op).symm)
    (ModuleCat.of Γ(X, Z.left) Γ(F, Z.left))).symm

/-- The isomorphism `rescaleSource` is the identity on underlying sections. -/
@[simp]
public theorem rescaleSource_hom_apply (iX : X ⟶ S) (F : X.Modules) (Z : Over (⊤ : X.Opens))
    (a : Γ(F, Z.left)) :
    letI := baseModule iX F Z.left
    (rescaleSource iX F Z).hom a = a := rfl

/-- **The rescaling upstairs**, the same statement for a morphism `k : Y ⟶ T` and a module on
`Y`, read in the direction the assembly uses. -/
public def rescaleTarget (k : Y ⟶ T) (G : Y.Modules) (Z : Over (⊤ : Y.Opens)) :
    letI := baseModule k G Z.left
    ModuleCat.of Γ(T, ⊤) Γ(G, Z.left) ≅
      (baseRestrictScalars k).obj ((sectionsPresheaf (⊤ : Y.Opens) G).obj (op Z)) :=
  letI := baseModule k G Z.left
  ModuleCat.restrictScalarsComp'App
    (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom
    (Y.presheaf.map (homOfLE (leOfHom Z.hom)).op).hom
    (k.appLE ⊤ Z.left (le_preimage_top k Z.left)).hom
    (by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom
        (Scheme.Hom.appLE_map k (le_preimage_top k ⊤) (homOfLE (leOfHom Z.hom)).op).symm)
    (ModuleCat.of Γ(Y, Z.left) Γ(G, Z.left))

/-- The isomorphism `rescaleTarget` is the identity on underlying sections. -/
@[simp]
public theorem rescaleTarget_hom_apply (k : Y ⟶ T) (G : Y.Modules) (Z : Over (⊤ : Y.Opens))
    (a : Γ(G, Z.left)) :
    letI := baseModule k G Z.left
    (rescaleTarget k G Z).hom a = a := rfl

/-- **Sections over two equal opens**, as an isomorphism of `Γ(T, ⊤)`-modules for the base
scalar structures: restriction along the equality, which is invertible because the two
restrictions compose to restriction along an identity. -/
public def baseSectionsEq (k : Y ⟶ T) (G : Y.Modules) {V V' : Y.Opens} (hV : V = V') :
    letI := baseModule k G V
    letI := baseModule k G V'
    ModuleCat.of Γ(T, ⊤) Γ(G, V) ≅ ModuleCat.of Γ(T, ⊤) Γ(G, V') :=
  letI := baseModule k G V
  letI := baseModule k G V'
  { hom := ModuleCat.ofHom (baseResHom k G hV.ge)
    inv := ModuleCat.ofHom (baseResHom k G hV.le)
    hom_inv_id := by subst hV; ext a; simp [baseResHom]
    inv_hom_id := by subst hV; ext a; simp [baseResHom] }

/-- The forward map of `baseSectionsEq hV` is restriction of sections from `V` to `V'`. -/
@[simp]
public theorem baseSectionsEq_hom_apply (k : Y ⟶ T) (G : Y.Modules) {V V' : Y.Opens}
    (hV : V = V') (a : Γ(G, V)) :
    letI := baseModule k G V
    letI := baseModule k G V'
    (baseSectionsEq k G hV).hom a = (G.presheaf.map (homOfLE hV.ge).op).hom a := rfl

/-! ### The degreewise comparison, as an isomorphism of modules -/

/-- **The degreewise comparison over an affine open, as an isomorphism of `Γ(T, ⊤)`-modules.**
This is `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap` together with its
bijectivity; no flatness is involved. -/
public def degreewiseIso (H : IsPullback p k iX q) [IsAffine S] [IsAffine T] (F : X.Modules)
    [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W) :
    letI := baseModule iX F W
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
    (baseExtendScalars q).obj (ModuleCat.of Γ(S, ⊤) Γ(F, W)) ≅
      ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
  letI := baseAlgebra q
  letI := baseModule iX F W
  letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  (LinearEquiv.ofBijective (sectionsBaseChangeMap H F W)
    (bijective_sectionsBaseChangeMap_of_isAffineOpen H F hW)).toModuleIso

/-- The isomorphism `degreewiseIso` sends `b ⊗ₜ a` to `b` times the pullback of the section
`a`. -/
@[simp]
public theorem degreewiseIso_hom_tmul (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (b : Γ(T, ⊤)) (a : Γ(F, W)) :
    letI := baseModule iX F W
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
    (degreewiseIso H F hW).hom (b ⊗ₜ[Γ(S, ⊤)] a) = b • pullbackUnitSections p F W a := by
  let := baseAlgebra q
  let := baseModule iX F W
  let := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  exact sectionsBaseChangeMap_tmul H F W b a

/-! ### The cover and its preimage -/

section Cover

/-- The preimages of the members of a covering of `X` cover `Y`, in the orientation
`Stacks.Cohomology.CechSheaf.cechComplex` asks for. -/
public theorem top_eq_iSup_preimage {ι : Type u} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) (p : Y ⟶ X) : (⊤ : Y.Opens) = ⨆ i, p ⁻¹ᵁ U i :=
  (p.iSup_preimage_eq_top hU.symm).symm

/-- A nonempty intersection of members of the covering, viewed in the slice over `⊤`, is affine
as soon as the finite intersections of the covering are. -/
public theorem isAffineOpen_inter_coverObject {ι : Type u} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a)))
    {m : ℕ} (x : Fin (m + 1) → ι) :
    IsAffineOpen (inter (coverObject U hU) x).left := by
  rw [inter_coverObject_left, inter_eq_iInf]
  exact hUaff x

/-- **The preimage of an intersection of members is the corresponding intersection of the
preimages.** -/
public theorem preimage_inter_coverObject {ι : Type u} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) (p : Y ⟶ X) {m : ℕ} (x : Fin (m + 1) → ι) :
    p ⁻¹ᵁ (inter (coverObject U hU) x).left =
      (inter (coverObject (fun i => p ⁻¹ᵁ U i) (top_eq_iSup_preimage U hU p)) x).left := by
  rw [inter_coverObject_left, inter_coverObject_left, inter_eq_iInf, inter_eq_iInf,
    Stacks.ProjectiveCohomology.preimage_iInf]

end Cover

/-! ### The comparison at one tuple -/

variable (H : IsPullback p k iX q)

/-- **The comparison at a nonempty tuple of members of the covering**, in the shape the generic
assembly `Stacks.CategoryTheory.CechComplex.cechComparisonIsoOfAdditive` consumes: the
affine base-change isomorphism, bracketed by the two identity-on-carriers rescalings and by the
transport along the identification of the preimage of an intersection with the intersection of
the preimages. -/
public def comparisonDeg [IsAffine S] [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a)))
    {m : ℕ} (x : Fin (m + 1) → ι) :
    (baseRestrictScalars iX ⋙ baseExtendScalars q).obj
        ((sectionsPresheaf (⊤ : X.Opens) F).obj (op (inter (coverObject U hU) x))) ≅
      (baseRestrictScalars k).obj
        ((sectionsPresheaf (⊤ : Y.Opens) ((Scheme.Modules.pullback p).obj F)).obj
          (op (inter (coverObject (fun i => p ⁻¹ᵁ U i) (top_eq_iSup_preimage U hU p)) x))) :=
  (baseExtendScalars q).mapIso (rescaleSource iX F (inter (coverObject U hU) x)) ≪≫
    degreewiseIso H F (isAffineOpen_inter_coverObject U hU hUaff x) ≪≫
    baseSectionsEq k ((Scheme.Modules.pullback p).obj F)
      (preimage_inter_coverObject U hU p x) ≪≫
    rescaleTarget k ((Scheme.Modules.pullback p).obj F) _

/-- **The comparison, on elements.** Every step but the degreewise comparison itself is the
identity on carriers, so the formula holds by `rfl`. -/
public theorem comparisonDeg_hom_tmul [IsAffine S] [IsAffine T] (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a)))
    {m : ℕ} (x : Fin (m + 1) → ι) (b : Γ(T, ⊤))
    (a : Γ(F, (inter (coverObject U hU) x).left)) :
    letI := baseModule k ((Scheme.Modules.pullback p).obj F)
      (p ⁻¹ᵁ (inter (coverObject U hU) x).left)
    (comparisonDeg H F U hU hUaff x).hom (b ⊗ₜ[Γ(S, ⊤)] a) =
      (((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (preimage_inter_coverObject U hU p x).ge).op).hom
        (b • pullbackUnitSections p F (inter (coverObject U hU) x).left a) := rfl

/-- **The comparisons commute with the reindexing maps.** The Čech differential is an
alternating sum of restrictions, so this is the compatibility that makes the family of
comparisons a map of Čech complexes. It is one application of
`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_naturality`: the two
rescalings and the transport are restrictions of sections, and restrictions compose. -/
public theorem comparisonDeg_comm [IsAffine S] [IsAffine T] (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a)))
    {m m' : ℕ} (x : Fin (m + 1) → ι) (h : Fin (m' + 1) → Fin (m + 1)) :
    (comparisonDeg H F U hU hUaff (x ∘ h)).hom ≫
        (baseRestrictScalars k).map ((sectionsPresheaf (⊤ : Y.Opens)
          ((Scheme.Modules.pullback p).obj F)).map
            (interMap (coverObject (fun i => p ⁻¹ᵁ U i) (top_eq_iSup_preimage U hU p)) x h).op) =
      (baseRestrictScalars iX ⋙ baseExtendScalars q).map
          ((sectionsPresheaf (⊤ : X.Opens) F).map (interMap (coverObject U hU) x h).op) ≫
        (comparisonDeg H F U hU hUaff x).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro a
  let := baseModule k ((Scheme.Modules.pullback p).obj F)
    (p ⁻¹ᵁ (inter (coverObject U hU) (x ∘ h)).left)
  let := baseModule k ((Scheme.Modules.pullback p).obj F)
    (p ⁻¹ᵁ (inter (coverObject U hU) x).left)
  show Stacks.Cohomology.Basis.res ((Scheme.Modules.pullback p).obj F).presheaf
        (leOfHom (interMap (coverObject (fun i => p ⁻¹ᵁ U i)
          (top_eq_iSup_preimage U hU p)) x h).left)
        (Stacks.Cohomology.Basis.res ((Scheme.Modules.pullback p).obj F).presheaf
          (preimage_inter_coverObject U hU p (x ∘ h)).ge
          ((1 : Γ(T, ⊤)) • pullbackUnitSections p F
            (inter (coverObject U hU) (x ∘ h)).left a)) =
      Stacks.Cohomology.Basis.res ((Scheme.Modules.pullback p).obj F).presheaf
        (preimage_inter_coverObject U hU p x).ge
        ((1 : Γ(T, ⊤)) • pullbackUnitSections p F (inter (coverObject U hU) x).left
          (Stacks.Cohomology.Basis.res F.presheaf
            (leOfHom (interMap (coverObject U hU) x h).left) a))
  have hnat : Stacks.Cohomology.Basis.res ((Scheme.Modules.pullback p).obj F).presheaf
        (Scheme.Hom.preimage_mono p (leOfHom (interMap (coverObject U hU) x h).left))
        (pullbackUnitSections p F (inter (coverObject U hU) (x ∘ h)).left a) =
      pullbackUnitSections p F (inter (coverObject U hU) x).left
        (Stacks.Cohomology.Basis.res F.presheaf
          (leOfHom (interMap (coverObject U hU) x h).left) a) :=
    (pullbackUnitSections_naturality p F
      (leOfHom (interMap (coverObject U hU) x h).left) a).symm
  rw [one_smul, one_smul, Stacks.Cohomology.Basis.res_res, ← hnat,
    Stacks.Cohomology.Basis.res_res]

/-! ### The comparison of Čech complexes -/

/-- **The Čech complex of the preimage cover is the base change of the Čech complex.** For a
cartesian square with affine base, a quasi-coherent `F` and a finite cover of `X` whose nonempty
finite intersections are affine, the Čech complex of the preimage cover of `p^* F` is the base
change along `Γ(S, ⊤) ⟶ Γ(T, ⊤)` of the Čech complex of `U` and `F`.

This is the sentence *"we have the following relation between the Čech complexes"* in the proof
of [Stacks, Tag 02KH] part (2). It needs no flatness: only additivity of the two
change-of-rings functors, through which the degree-`n` terms — products over
`Fin (n + 1) → ι` — are preserved. -/
public def cechBaseChangeIso [IsAffine S] [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a))) :
    ((baseRestrictScalars iX ⋙ baseExtendScalars q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (cechComplex.{u, u, u, u} (R := X.ringCatSheaf) (⊤ : X.Opens) U hU F) ≅
      ((baseRestrictScalars k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex.{u, u, u, u} (R := Y.ringCatSheaf) (⊤ : Y.Opens) (fun i => p ⁻¹ᵁ U i)
          (top_eq_iSup_preimage U hU p) ((Scheme.Modules.pullback p).obj F)) :=
  cechComparisonIsoOfAdditive _ _ _ _ _ _
    (fun x => comparisonDeg H F U hU hUaff x)
    (fun x h => comparisonDeg_comm H F U hU hUaff x h)

/-- **The comparison of Čech complexes, for a second cover identified memberwise with the
preimage cover.** The two covering hypotheses are propositions, so once the covers are
identified nothing further has to be transported. -/
public def cechBaseChangeIsoOfPreimage [IsAffine S] [IsAffine T] (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a)))
    (U' : ι → Y.Opens) (hUU' : ∀ i, p ⁻¹ᵁ U i = U' i) (hU' : (⊤ : Y.Opens) = ⨆ i, U' i) :
    ((baseRestrictScalars iX ⋙ baseExtendScalars q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (cechComplex.{u, u, u, u} (R := X.ringCatSheaf) (⊤ : X.Opens) U hU F) ≅
      ((baseRestrictScalars k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex.{u, u, u, u} (R := Y.ringCatSheaf) (⊤ : Y.Opens) U' hU'
          ((Scheme.Modules.pullback p).obj F)) := by
  obtain rfl : (fun i => p ⁻¹ᵁ U i) = U' := funext hUU'
  exact cechBaseChangeIso H F U hU hUaff

end Stacks.AlgebraicGeometry.SectionsBaseChange

namespace Stacks.ProjectiveCohomology

open Stacks.AlgebraicGeometry.SectionsBaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- **The Čech complexes of the standard covers of projective space are compared by base
change.** For a ring map `A ⟶ B` and a quasi-coherent module `F` on `ℙⁿ_A`, the Čech complex of
the `n + 1` standard charts of `ℙⁿ_B` with coefficients in the pullback of `F` is the base
change along `A ⟶ B` of the Čech complex of the standard charts of `ℙⁿ_A` with coefficients in
`F`.

The intersections of charts are affine by
`Stacks.ProjectiveCohomology.isAffineOpen_iInf_chartAtUniverse`, and the charts of `ℙⁿ_B` are
*equal* to the preimages of those of `ℙⁿ_A` by
`Stacks.ProjectiveCohomology.preimage_chartAtUniverse`. No flatness of `A ⟶ B` is used; it is
needed only to pass from these complexes to their cohomology. -/
public def cechBaseChangeIsoChart (F : (projectiveSpaceOverRing n A).Modules)
    [F.IsQuasicoherent] :
    ((baseRestrictScalars (pullback.fst (terminal.from (Spec A))
              (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⋙
          baseExtendScalars (Spec.map φ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Stacks.Cohomology.CechSheaf.cechComplex.{u, u, u, u}
          (R := (projectiveSpaceOverRing n A).ringCatSheaf) ⊤ (chartAtUniverse n A)
          (iSup_chartAtUniverse_eq_top n A).symm F) ≅
      ((baseRestrictScalars (pullback.fst (terminal.from (Spec B))
            (terminal.from (projectiveSpaceAtUniverse.{u} n)))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (Stacks.Cohomology.CechSheaf.cechComplex.{u, u, u, u}
          (R := (projectiveSpaceOverRing n B).ringCatSheaf) ⊤ (chartAtUniverse n B)
          (iSup_chartAtUniverse_eq_top n B).symm
          ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n φ)).obj F)) :=
  cechBaseChangeIsoOfPreimage (isPullback_projectiveSpaceOverMap n (Spec.map φ)) F
    (chartAtUniverse n A) (iSup_chartAtUniverse_eq_top n A).symm
    (fun x => isAffineOpen_iInf_chartAtUniverse n A x)
    (chartAtUniverse n B) (preimage_chartAtUniverse n φ)
    (iSup_chartAtUniverse_eq_top n B).symm

end Stacks.ProjectiveCohomology

end
