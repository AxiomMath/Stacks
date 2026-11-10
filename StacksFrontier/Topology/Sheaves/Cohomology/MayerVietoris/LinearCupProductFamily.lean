module

public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearDerivedSections

/-!
# The `A`-linear cup product at an arbitrary open

Let `(X, 𝒪_X)` be a ringed space and let `A = Γ(X, 𝒪_X)`.  For complexes `𝒦` and `ℐ` of
`𝒪_X`-modules and an open `W ⊆ X` there is a map of complexes of `A`-modules

`Tot(Γ(W, 𝒦) ⊗_A Γ(W, ℐ)) ⟶ Γ(W, Tot(𝒦 ⊗_{𝒪_X} ℐ))`,

assembled from the maps `Γ(W, 𝒦^p) ⊗_A Γ(W, ℐ^q) ⟶ Γ(W, 𝒦^p ⊗_{𝒪_X} ℐ^q)` on sections, and it
commutes with the restriction maps of an inclusion `Z ⊆ W` of opens.  Combined with a map of
complexes `T ⟶ Γ(X, 𝒦)` of `A`-modules and a quasi-isomorphism `Tot(𝒦 ⊗_{𝒪_X} ℐ) ⟶ 𝒥` this
produces, for every `W` at once, a map of complexes of `A`-modules

`Tot(T ⊗_A Γ(W, ℐ)) ⟶ Γ(W, 𝒥)`

compatible with restriction, which for suitable choices of `T`, `𝒦`, `ℐ` and `𝒥` represents the
map `RΓ(X, K) ⊗^𝐋_A RΓ(W, M) ⟶ RΓ(W, K ⊗^𝐋_{𝒪_X} M)` in `D(A)`.

## Main definitions

* `Stacks.Cohomology.LinearCupProductFamily.openSections` — sections over an open `W ⊆ X` as
  `A`-modules, with `Stacks.Cohomology.LinearCupProductFamily.openRestriction` the restriction
  transformation attached to an inclusion `Z ⊆ W`.
* `Stacks.Cohomology.LinearCupProductFamily.sectionsTensor` — the comparison
  `Γ(W, F) ⊗_A Γ(W, G) ⟶ Γ(W, F ⊗_{𝒪_X} G)` of `A`-modules.
* `Stacks.Cohomology.LinearCupProductFamily.mapBifunctorBicomplexMap` and
  `Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap` — a degreewise comparison of
  two bifunctors along an additive functor, as a map of the associated bicomplexes and of their
  total complexes.
* `Stacks.Cohomology.LinearCupProductFamily.sectionsTensorTotal` — the comparison on total
  complexes, `Tot(Γ(W, 𝒦) ⊗_A Γ(W, ℐ)) ⟶ Γ(W, Tot(𝒦 ⊗_{𝒪_X} ℐ))`.
* `Stacks.Cohomology.LinearCupProductFamily.CupData` — a choice of resolutions for a pair of
  complexes `K`, `M` of `𝒪_X`-modules: a K-flat complex `T` of flat `A`-modules with a map
  `T ⟶ Γ(X, 𝒦)` exhibiting it as a representative of `RΓ(X, K)`, a K-flat complex `𝒦` of flat
  `𝒪_X`-modules resolving `K`, a K-injective complex `ℐ` with injective terms resolving `M`, and
  a quasi-isomorphism `Tot(𝒦 ⊗_{𝒪_X} ℐ) ⟶ 𝒥` into a K-injective complex with injective terms.
* `Stacks.Cohomology.LinearCupProductFamily.CupData.cupMap` — the resulting map of complexes
  `Tot(T ⊗_A Γ(W, ℐ)) ⟶ Γ(W, 𝒥)`.

## Main results

* `Stacks.Cohomology.LinearCupProductFamily.sectionsTensor_naturality_left` and
  `Stacks.Cohomology.LinearCupProductFamily.sectionsTensor_naturality_right` — the comparison on
  sections is natural in each sheaf of modules.
* `Stacks.Cohomology.LinearCupProductFamily.sectionsTensor_restriction` — it commutes with
  restriction to a smaller open.
* `Stacks.Cohomology.LinearCupProductFamily.totalMap_naturality_functor` — the canonical map
  `Tot(Φ(C)) ⟶ Φ(Tot(C))` is natural in the additive functor `Φ`; and
  `Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap_naturality_functor`, the same
  for the comparison attached to a degreewise comparison of bifunctors.
* `Stacks.Cohomology.LinearCupProductFamily.mapBifunctorMap_comp` — maps of total complexes of a
  bifunctor compose componentwise.
* `Stacks.Cohomology.LinearCupProductFamily.sectionsTensorTotal_restriction` — the comparison on
  total complexes commutes with restriction to a smaller open.
* `Stacks.Cohomology.LinearCupProductFamily.CupData.cupMap_restriction` — the family
  `Tot(T ⊗_A Γ(W, ℐ)) ⟶ Γ(W, 𝒥)` commutes with restriction to a smaller open, on the nose.

## Implementation notes

The comparison `Γ(W, F) ⊗_A Γ(W, G) ⟶ Γ(W, F ⊗_{𝒪_X} G)` is the sheafification unit of the
presheaf tensor product, read on sections over `W` and precomposed with the canonical map from
the tensor product over `A = Γ(X, 𝒪_X)` to the tensor product over `Γ(W, 𝒪_X)`.  Both factors
are recorded at once by giving the bilinear map `(s, t) ↦ s ⊗ t` directly over `A`: the scalars
of `A` act on sections over `W` through the restriction homomorphism `A ⟶ Γ(W, 𝒪_X)`, so a map
which is `Γ(W, 𝒪_X)`-bilinear is in particular `A`-bilinear.

Passing from sections to complexes is done in two steps.  A degreewise comparison of bifunctors
gives a map of bicomplexes, `mapBifunctorBicomplexMap`; and for an additive functor `Φ` there is
a canonical map `Tot(Φ(C)) ⟶ Φ(Tot(C))` out of the total complex of the termwise image of a
bicomplex, `HomologicalComplex₂.totalMap`, because the source is a coproduct in each degree
while the target need not be.  Sections over an open do not commute with the infinite direct
sums forming a total complex, which is why only a map and not an isomorphism is available; it is
however the direction needed, and that is all the construction uses.

The compatibility of the family with restriction is not checked summand by summand.  Each of
the three factors of `CupData.cupMap` has its own restriction square — naturality of the
sections of a fixed map of complexes of sheaves, `sectionsTensorTotal_restriction`, and the
functoriality of `T ⟶ Γ(W, 𝒦)` in `W` — and the squares compose, which is what makes the
compatibility hold on the nose rather than up to homotopy.

Everything is stated at the spelling `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` of the
structure sheaf, through the abbreviation
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`: the instance arguments of the
tensor product of sheaves of modules fix the ring sheaf at that spelling, and additivity of the
termwise sections is not available at any other.  For the same reason `openSections` repeats the
composite defining `Stacks.Cohomology.LinearDerivedSections.linearSections`, with which it
agrees by `openSections_eq`.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0G6X](https://stacks.math.columbia.edu/tag/0G6X)
* [Stacks Project, Tag 0G6V](https://stacks.math.columbia.edu/tag/0G6V)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.LinearDerivedSections
open Stacks.SheafOfModules.Tensor
open scoped TensorProduct

universe u

namespace Stacks.Cohomology.LinearCupProductFamily

variable (X : RingedSpace.{u, u})

/-- The sections of the structure sheaf over an open form a commutative ring. -/
instance sectionsCommRing (W : Opens X.carrier) :
    CommRing ((ringSheaf X.sheaf).obj.obj (op W)) :=
  inferInstanceAs (CommRing (X.presheaf.obj (op W)))

/-- **`A`-linear sections over an open**, `Γ(W, -) : Mod(𝒪_X) ⥤ Mod(A)` for `A = Γ(X, 𝒪_X)`:
the sections over `W` of a sheaf of `𝒪_X`-modules, regarded as a module over `A` by restriction
of scalars along `A ⟶ Γ(W, 𝒪_X)`. -/
abbrev openSections (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    Modules X ⥤ ModuleCat.{u} (baseRing X) :=
  sectionsOverOpen X W ⋙ ModuleCat.restrictScalars (fromTop X W).hom

/-- `A`-linear sections over an open are additive: addition of sections is computed open by open
and restriction of scalars does not change the underlying group. -/
instance openSections_additive (W : Opens X.carrier) : (openSections X W).Additive where
  map_add := rfl

/-- Sections over an open with scalars restricted to `A` are the functor whose right derived
functor is `RΓ(W, -) : D(𝒪_X) ⥤ D(A)`. -/
theorem openSections_eq (W : Opens X.carrier) : openSections X W = linearSections X W := rfl

/-- **Restriction of `A`-linear sections** to a smaller open. -/
def openRestriction {X : RingedSpace.{u, u}} {Z W : Opens X.carrier} (h : Z ≤ W) :
    openSections X W ⟶ openSections X Z :=
  linearRestriction X h

/-- Restriction of `A`-linear sections is the restriction map of the underlying presheaf of
modules. -/
theorem openRestriction_app_apply {X : RingedSpace.{u, u}} {Z W : Opens X.carrier} (h : Z ≤ W)
    (M : Modules X) (x : (M.val.obj (op W) : Type u)) :
    ((openRestriction h).app M).hom x = M.val.map (homOfLE h).op x :=
  rfl

/-! ### The comparison on sections -/

variable (W : Opens X.carrier)

/-- The unit of the sheafification adjunction at the presheaf tensor product: the canonical
morphism `F ⊗^{pre}_{𝒪_X} G ⟶ F ⊗_{𝒪_X} G` of presheaves of `𝒪_X`-modules. -/
abbrev tensorUnit (F G : Modules X) :
    ((PresheafOfModules.tensorBifunctor X.presheaf).obj F.val).obj G.val ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf X.sheaf).obj)).obj
        ((SheafOfModules.forget _).obj (((sheafTensor X.sheaf).obj F).obj G)) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf X.sheaf).obj)).unit.app _

variable {X}

/-- The section of `F ⊗_{𝒪_X} G` over `W` determined by a section of `F` and a section of `G`
over `W`. -/
abbrev tmulSection (F G : Modules X) (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    (((sheafTensor X.sheaf).obj F).obj G).val.obj (op W) :=
  ((tensorUnit X F G).app (op W)).hom (s ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t)

variable (F G : Modules X)

/-- Pairing of sections turns a sum of pure tensors into a sum. -/
private theorem tmulSection_eq_add {s t s₁ t₁ s₂ t₂ : _}
    (h : s ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t =
      s₁ ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t₁ +
        s₂ ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t₂) :
    tmulSection W F G s t = tmulSection W F G s₁ t₁ + tmulSection W F G s₂ t₂ :=
  (congrArg ((tensorUnit X F G).app (op W)).hom h).trans (map_add _ _ _)

/-- Pairing of sections turns a scalar multiple of a pure tensor into a scalar multiple. -/
private theorem tmulSection_eq_smul {c : (ringSheaf X.sheaf).obj.obj (op W)} {s t s' t' : _}
    (h : s ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t =
      c • s' ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t') :
    tmulSection W F G s t = c • tmulSection W F G s' t' :=
  (congrArg ((tensorUnit X F G).app (op W)).hom h).trans (LinearMap.map_smul _ _ _)

/-- The pairing of sections is additive in its first argument. -/
theorem tmulSection_add_left (s₁ s₂ : F.val.obj (op W)) (t : G.val.obj (op W)) :
    tmulSection W F G (s₁ + s₂) t = tmulSection W F G s₁ t + tmulSection W F G s₂ t :=
  tmulSection_eq_add W F G (TensorProduct.add_tmul _ _ _)

/-- The pairing of sections is homogeneous in its first argument. -/
theorem tmulSection_smul_left (c : (ringSheaf X.sheaf).obj.obj (op W))
    (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    tmulSection W F G (c • s) t = c • tmulSection W F G s t :=
  tmulSection_eq_smul W F G (TensorProduct.smul_tmul' _ _ _)

/-- The pairing of sections is additive in its second argument. -/
theorem tmulSection_add_right (s : F.val.obj (op W)) (t₁ t₂ : G.val.obj (op W)) :
    tmulSection W F G s (t₁ + t₂) = tmulSection W F G s t₁ + tmulSection W F G s t₂ :=
  tmulSection_eq_add W F G (TensorProduct.tmul_add _ _ _)

/-- The pairing of sections is homogeneous in its second argument. -/
theorem tmulSection_smul_right (c : (ringSheaf X.sheaf).obj.obj (op W))
    (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    tmulSection W F G s (c • t) = c • tmulSection W F G s t :=
  tmulSection_eq_smul W F G (TensorProduct.tmul_smul _ _ _)

/-- The pairing of sections over `W`, as an `A`-bilinear map for `A = Γ(X, 𝒪_X)`: the scalars of
`A` act on sections over `W` through the restriction homomorphism `A ⟶ Γ(W, 𝒪_X)`. -/
def sectionsTensorBilinear :
    ((openSections X W).obj F) →ₗ[baseRing X]
      ((openSections X W).obj G) →ₗ[baseRing X]
        ((openSections X W).obj (((sheafTensor X.sheaf).obj F).obj G)) :=
  LinearMap.mk₂ (baseRing X)
    (fun s t => tmulSection W F G s t)
    (fun s₁ s₂ t => tmulSection_add_left W F G s₁ s₂ t)
    (fun c s t => tmulSection_smul_left W F G ((fromTop X W).hom c) s t)
    (fun s t₁ t₂ => tmulSection_add_right W F G s t₁ t₂)
    (fun c s t => tmulSection_smul_right W F G ((fromTop X W).hom c) s t)

/-- **The comparison on sections** `Γ(W, F) ⊗_A Γ(W, G) ⟶ Γ(W, F ⊗_{𝒪_X} G)`, a map of
`A`-modules for `A = Γ(X, 𝒪_X)`. -/
def sectionsTensor :
    ((openSections X W).obj F ⊗ (openSections X W).obj G : ModuleCat.{u} (baseRing X)) ⟶
      (openSections X W).obj (((sheafTensor X.sheaf).obj F).obj G) :=
  ModuleCat.ofHom
    (X := ((openSections X W).obj F ⊗ (openSections X W).obj G : ModuleCat.{u} (baseRing X)))
    (Y := (openSections X W).obj (((sheafTensor X.sheaf).obj F).obj G))
    (TensorProduct.lift (sectionsTensorBilinear W F G))

/-- The comparison on sections sends a pure tensor of sections to the corresponding section of
the tensor product. -/
theorem sectionsTensor_tmul (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    (sectionsTensor W F G).hom (s ⊗ₜ[baseRing X] t) = tmulSection W F G s t := rfl

variable {F G}

/-- The pairing of sections is natural in the first sheaf of modules. -/
theorem tmulSection_map_left {F' : Modules X} (f : F ⟶ F')
    (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    ((((sheafTensor X.sheaf).map f).app G).val.app (op W)).hom (tmulSection W F G s t) =
      tmulSection W F' G ((f.val.app (op W)).hom s) t :=
  (congrArg
    (fun k => (PresheafOfModules.Hom.app k (op W)).hom
      (s ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf X.sheaf).obj)).unit.naturality
        (((PresheafOfModules.tensorBifunctor X.presheaf).map f.val).app G.val))).symm

/-- The pairing of sections is natural in the second sheaf of modules. -/
theorem tmulSection_map_right {G' : Modules X} (g : G ⟶ G')
    (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    ((((sheafTensor X.sheaf).obj F).map g).val.app (op W)).hom (tmulSection W F G s t) =
      tmulSection W F G' s ((g.val.app (op W)).hom t) :=
  (congrArg
    (fun k => (PresheafOfModules.Hom.app k (op W)).hom
      (s ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf X.sheaf).obj)).unit.naturality
        (((PresheafOfModules.tensorBifunctor X.presheaf).obj F.val).map g.val))).symm

/-- Restricting the pairing of two sections restricts the two sections. -/
theorem tmulSection_restrict {Z : Opens X.carrier} (h : Z ≤ W)
    (s : F.val.obj (op W)) (t : G.val.obj (op W)) :
    ((((sheafTensor X.sheaf).obj F).obj G).val.map (homOfLE h).op).hom
        (tmulSection W F G s t) =
      tmulSection Z F G ((F.val.map (homOfLE h).op).hom s) ((G.val.map (homOfLE h).op).hom t) :=
  (PresheafOfModules.naturality_apply (tensorUnit X F G) (homOfLE h).op
    (s ⊗ₜ[(ringSheaf X.sheaf).obj.obj (op W)] t)).symm

/-- **The comparison on sections is natural in the first sheaf of modules.** -/
theorem sectionsTensor_naturality_left {F' : Modules X} (f : F ⟶ F') :
    ((openSections X W).map f ▷ (openSections X W).obj G) ≫ sectionsTensor W F' G =
      sectionsTensor W F G ≫
        (openSections X W).map (((sheafTensor X.sheaf).map f).app G) :=
  ModuleCat.MonoidalCategory.tensor_ext fun s t => (tmulSection_map_left W f s t).symm

/-- **The comparison on sections is natural in the second sheaf of modules.** -/
theorem sectionsTensor_naturality_right {G' : Modules X} (g : G ⟶ G') :
    ((openSections X W).obj F ◁ (openSections X W).map g) ≫ sectionsTensor W F G' =
      sectionsTensor W F G ≫
        (openSections X W).map (((sheafTensor X.sheaf).obj F).map g) :=
  ModuleCat.MonoidalCategory.tensor_ext fun s t => (tmulSection_map_right W g s t).symm

/-- **The comparison on sections commutes with restriction** to a smaller open. -/
theorem sectionsTensor_restriction {Z : Opens X.carrier} (h : Z ≤ W) :
    sectionsTensor W F G ≫
        (openRestriction h).app (((sheafTensor X.sheaf).obj F).obj G) =
      ((openRestriction h).app F ⊗ₘ (openRestriction h).app G) ≫
        sectionsTensor Z F G :=
  ModuleCat.MonoidalCategory.tensor_ext fun s t => tmulSection_restrict W h s t

/-! ### A degreewise comparison of bifunctors, on total complexes -/

section Bicomplex

universe vA vB vD vA' vB' vD' uA uB uD uA' uB' uD'

variable {CA : Type uA} {CB : Type uB} {CD : Type uD} {CA' : Type uA'} {CB' : Type uB'}
  {CD' : Type uD'} [Category.{vA} CA] [Category.{vB} CB] [Category.{vD} CD]
  [Category.{vA'} CA'] [Category.{vB'} CB'] [Category.{vD'} CD']
  [Preadditive CA] [Preadditive CB] [Preadditive CD]
  [Preadditive CA'] [Preadditive CB'] [Preadditive CD']
  (E : CA ⥤ CB ⥤ CD) (E' : CA' ⥤ CB' ⥤ CD')
  [E.PreservesZeroMorphisms] [∀ a, (E.obj a).PreservesZeroMorphisms]
  [E'.PreservesZeroMorphisms] [∀ a, (E'.obj a).PreservesZeroMorphisms]
  (Φ₁ : CA ⥤ CA') (Φ₂ : CB ⥤ CB') (Φ : CD ⥤ CD') [Φ₁.Additive] [Φ₂.Additive] [Φ.Additive]
  (ε : ∀ (a : CA) (b : CB), (E'.obj (Φ₁.obj a)).obj (Φ₂.obj b) ⟶ Φ.obj ((E.obj a).obj b))
  (hε₁ : ∀ {a a' : CA} (f : a ⟶ a') (b : CB),
    (E'.map (Φ₁.map f)).app (Φ₂.obj b) ≫ ε a' b = ε a b ≫ Φ.map ((E.map f).app b))
  (hε₂ : ∀ (a : CA) {b b' : CB} (g : b ⟶ b'),
    (E'.obj (Φ₁.obj a)).map (Φ₂.map g) ≫ ε a b' = ε a b ≫ Φ.map ((E.obj a).map g))
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

include hε₁ hε₂ in
/-- A degreewise comparison `E'(Φ₁ a, Φ₂ b) ⟶ Φ(E(a, b))` of two bifunctors along an additive
functor `Φ`, read on the bicomplexes attached to a pair of complexes.  The bicomplexes carry no
Koszul signs, so the two commutation obligations are the naturality of the comparison in its
first and in its second variable. -/
def mapBifunctorBicomplexMap (K : HomologicalComplex CA c₁) (L : HomologicalComplex CB c₂) :
    ((E'.mapBifunctorHomologicalComplex c₁ c₂).obj
          ((Φ₁.mapHomologicalComplex c₁).obj K)).obj ((Φ₂.mapHomologicalComplex c₂).obj L) ⟶
      HomologicalComplex₂.mapBicomplex Φ
        (((E.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L) where
  f i₁ :=
    { f := fun i₂ => ε (K.X i₁) (L.X i₂)
      comm' := fun i₂ i₂' _ => (hε₂ (K.X i₁) (L.d i₂ i₂')).symm }
  comm' i₁ i₁' _ := by
    ext i₂
    exact (hε₁ (K.d i₁ i₁') (L.X i₂)).symm

variable {I₁₂ : Type*} (c : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c] [DecidableEq I₁₂]
  (K : HomologicalComplex CA c₁) (L : HomologicalComplex CB c₂)
  [HomologicalComplex.HasMapBifunctor K L E c]
  [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
    ((Φ₂.mapHomologicalComplex c₂).obj L) E' c]
  [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
    (((E.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)) c]

include hε₁ hε₂ in
/-- **The comparison of total complexes** attached to a degreewise comparison of bifunctors:

`Tot(E'(Φ₁ K, Φ₂ L)) ⟶ Φ(Tot(E(K, L)))`.

It is the comparison of bicomplexes followed by the canonical map out of the total complex of a
termwise image, which exists because that total complex is a coproduct in each degree. -/
def mapBifunctorTotalMap :
    HomologicalComplex.mapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
        ((Φ₂.mapHomologicalComplex c₂).obj L) E' c ⟶
      (Φ.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor K L E c) :=
  HomologicalComplex₂.total.map
      (mapBifunctorBicomplexMap E E' Φ₁ Φ₂ Φ ε hε₁ hε₂ c₁ c₂ K L) c ≫
    HomologicalComplex₂.totalMap Φ (((E.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)

end Bicomplex

/-! ### Naturality of the total-complex comparison in the functor -/

section TotalMapNatural

universe vD vD' uD uD'

variable {CD : Type uD} {CD' : Type uD'} [Category.{vD} CD] [Category.{vD'} CD']
  [Preadditive CD] [Preadditive CD']
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c] [DecidableEq I₁₂]
  {Φ Φ' : CD ⥤ CD'} [Φ.Additive] [Φ'.Additive] (η : Φ ⟶ Φ')
  (B : HomologicalComplex₂ CD c₁ c₂)

/-- A natural transformation of additive functors, applied to each term of a bicomplex. -/
abbrev mapBicomplexNatTrans :
    HomologicalComplex₂.mapBicomplex Φ B ⟶ HomologicalComplex₂.mapBicomplex Φ' B :=
  ((NatTrans.mapHomologicalComplex (NatTrans.mapHomologicalComplex η c₂) c₁)).app B

variable [B.HasTotal c] [(HomologicalComplex₂.mapBicomplex Φ B).HasTotal c]
  [(HomologicalComplex₂.mapBicomplex Φ' B).HasTotal c]

/-- **The canonical map `Tot(Φ(B)) ⟶ Φ(Tot(B))` is natural in the additive functor `Φ`.** -/
theorem totalMap_naturality_functor :
    HomologicalComplex₂.total.map (mapBicomplexNatTrans η B) c ≫
        HomologicalComplex₂.totalMap Φ' B =
      HomologicalComplex₂.totalMap Φ B ≫
        (NatTrans.mapHomologicalComplex η c).app (B.total c) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine HomologicalComplex₂.total.hom_ext c (fun i₁ i₂ hi => ?_)
  change (HomologicalComplex₂.mapBicomplex Φ B).ιTotal c i₁ i₂ n hi ≫
      ((HomologicalComplex₂.total.map (mapBicomplexNatTrans η B) c).f n ≫
        HomologicalComplex₂.totalMapf Φ' B n) =
    (HomologicalComplex₂.mapBicomplex Φ B).ιTotal c i₁ i₂ n hi ≫
      (HomologicalComplex₂.totalMapf Φ B n ≫ η.app ((B.total c).X n))
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
    HomologicalComplex₂.ι_totalMapf, ← Category.assoc, HomologicalComplex₂.ι_totalMapf]
  exact (η.naturality (B.ιTotal c i₁ i₂ n hi)).symm

end TotalMapNatural

/-! ### Naturality of the comparison of total complexes in the functor -/

section SingleFunctor

universe v v' uu uu'

variable {C : Type uu} {C' : Type uu'} [Category.{v} C] [Category.{v'} C']
  [Preadditive C] [Preadditive C']
  (E : C ⥤ C ⥤ C) (E' : C' ⥤ C' ⥤ C')
  [E.PreservesZeroMorphisms] [∀ a, (E.obj a).PreservesZeroMorphisms]
  [E'.PreservesZeroMorphisms] [∀ a, (E'.obj a).PreservesZeroMorphisms]
  {Φ Φ' : C ⥤ C'} [Φ.Additive] [Φ'.Additive]
  (ε : ∀ (a b : C), (E'.obj (Φ.obj a)).obj (Φ.obj b) ⟶ Φ.obj ((E.obj a).obj b))
  (hε₁ : ∀ {a a' : C} (f : a ⟶ a') (b : C),
    (E'.map (Φ.map f)).app (Φ.obj b) ≫ ε a' b = ε a b ≫ Φ.map ((E.map f).app b))
  (hε₂ : ∀ (a : C) {b b' : C} (g : b ⟶ b'),
    (E'.obj (Φ.obj a)).map (Φ.map g) ≫ ε a b' = ε a b ≫ Φ.map ((E.obj a).map g))
  (ε' : ∀ (a b : C), (E'.obj (Φ'.obj a)).obj (Φ'.obj b) ⟶ Φ'.obj ((E.obj a).obj b))
  (hε₁' : ∀ {a a' : C} (f : a ⟶ a') (b : C),
    (E'.map (Φ'.map f)).app (Φ'.obj b) ≫ ε' a' b = ε' a b ≫ Φ'.map ((E.map f).app b))
  (hε₂' : ∀ (a : C) {b b' : C} (g : b ⟶ b'),
    (E'.obj (Φ'.obj a)).map (Φ'.map g) ≫ ε' a b' = ε' a b ≫ Φ'.map ((E.obj a).map g))
  (η : Φ ⟶ Φ')
  (hη : ∀ a b : C, (E'.map (η.app a)).app (Φ.obj b) ≫
      (E'.obj (Φ'.obj a)).map (η.app b) ≫ ε' a b = ε a b ≫ η.app ((E.obj a).obj b))
  {I₁ I₁₂ : Type*} (c₁ : ComplexShape I₁) (c : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₁ c] [DecidableEq I₁₂]
  (K L : HomologicalComplex C c₁)

omit [DecidableEq I₁₂] in
include hε₁ hε₂ hη in
/-- The comparison of bicomplexes commutes with a natural transformation of the functors, as
soon as the degreewise comparisons do. -/
theorem mapBifunctorBicomplexMap_naturality_functor :
    mapBifunctorBicomplexMap E E' Φ Φ Φ ε hε₁ hε₂ c₁ c₁ K L ≫
        mapBicomplexNatTrans η (((E.mapBifunctorHomologicalComplex c₁ c₁).obj K).obj L) =
      (((E'.mapBifunctorHomologicalComplex c₁ c₁).map
              ((NatTrans.mapHomologicalComplex η c₁).app K)).app
            ((Φ.mapHomologicalComplex c₁).obj L) ≫
          ((E'.mapBifunctorHomologicalComplex c₁ c₁).obj
              ((Φ'.mapHomologicalComplex c₁).obj K)).map
            ((NatTrans.mapHomologicalComplex η c₁).app L)) ≫
        mapBifunctorBicomplexMap E E' Φ' Φ' Φ' ε' hε₁' hε₂' c₁ c₁ K L := by
  refine HomologicalComplex.hom_ext _ _ (fun i₁ => ?_)
  refine HomologicalComplex.hom_ext _ _ (fun i₂ => ?_)
  dsimp only [HomologicalComplex.comp_f]
  rw [Category.assoc]
  exact (hη (K.X i₁) (L.X i₂)).symm

include hε₁ hε₂ hη in
/-- **The comparison of total complexes commutes with a natural transformation of the
functors.** -/
theorem mapBifunctorTotalMap_naturality_functor
    [HomologicalComplex.HasMapBifunctor K L E c]
    [HomologicalComplex.HasMapBifunctor ((Φ.mapHomologicalComplex c₁).obj K)
      ((Φ.mapHomologicalComplex c₁).obj L) E' c]
    [HomologicalComplex.HasMapBifunctor ((Φ'.mapHomologicalComplex c₁).obj K)
      ((Φ'.mapHomologicalComplex c₁).obj L) E' c]
    [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
      (((E.mapBifunctorHomologicalComplex c₁ c₁).obj K).obj L)) c]
    [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ'
      (((E.mapBifunctorHomologicalComplex c₁ c₁).obj K).obj L)) c] :
    mapBifunctorTotalMap E E' Φ Φ Φ ε hε₁ hε₂ c₁ c₁ c K L ≫
        (NatTrans.mapHomologicalComplex η c).app
          (HomologicalComplex.mapBifunctor K L E c) =
      HomologicalComplex.mapBifunctorMap ((NatTrans.mapHomologicalComplex η c₁).app K)
          ((NatTrans.mapHomologicalComplex η c₁).app L) E' c ≫
        mapBifunctorTotalMap E E' Φ' Φ' Φ' ε' hε₁' hε₂' c₁ c₁ c K L := by
  have key := mapBifunctorBicomplexMap_naturality_functor E E' ε hε₁ hε₂ ε' hε₁' hε₂' η hη
    c₁ K L
  dsimp only [mapBifunctorTotalMap, HomologicalComplex.mapBifunctorMap]
  rw [Category.assoc,
    ← totalMap_naturality_functor η (((E.mapBifunctorHomologicalComplex c₁ c₁).obj K).obj L),
    ← Category.assoc, ← HomologicalComplex₂.total.map_comp, key,
    HomologicalComplex₂.total.map_comp, Category.assoc]

end SingleFunctor

/-! ### The comparison on total complexes -/

section Total

variable (X : RingedSpace.{u, u})

/-- **The comparison on total complexes**

`Tot(Γ(W, 𝒦) ⊗_A Γ(W, ℐ)) ⟶ Γ(W, Tot(𝒦 ⊗_{𝒪_X} ℐ))`,

a map of complexes of `A`-modules for `A = Γ(X, 𝒪_X)`.  It is the comparison on sections in each
bidegree, followed by the canonical map out of a total complex of termwise sections. -/
def sectionsTensorTotal (W : Opens X.carrier) (𝒦 ℐ : CochainComplex (Modules X) ℤ) :
    HomologicalComplex.mapBifunctor
        (((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒦)
        (((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℐ)
        (curriedTensor (ModuleCat.{u} (baseRing X))) (ComplexShape.up ℤ) ⟶
      ((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor 𝒦 ℐ (sheafTensor X.sheaf) (ComplexShape.up ℤ)) :=
  mapBifunctorTotalMap (sheafTensor X.sheaf) (curriedTensor (ModuleCat.{u} (baseRing X)))
    (openSections X W) (openSections X W) (openSections X W) (sectionsTensor W)
    (fun f b => sectionsTensor_naturality_left (G := b) W f)
    (fun a {b b'} g => sectionsTensor_naturality_right (F := a) (G := b) (G' := b') W g)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) 𝒦 ℐ

/-- **The comparison on total complexes commutes with restriction** to a smaller open: the two
total complexes are built from the fixed complexes `𝒦` and `ℐ` of sheaves, and the comparison is
induced by evaluating them on sections. -/
theorem sectionsTensorTotal_restriction {Z W : Opens X.carrier} (h : Z ≤ W)
    (𝒦 ℐ : CochainComplex (Modules X) ℤ) :
    sectionsTensorTotal X W 𝒦 ℐ ≫
        (NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app
          (HomologicalComplex.mapBifunctor 𝒦 ℐ (sheafTensor X.sheaf) (ComplexShape.up ℤ)) =
      HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app 𝒦)
          ((NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app ℐ)
          (curriedTensor (ModuleCat.{u} (baseRing X))) (ComplexShape.up ℤ) ≫
        sectionsTensorTotal X Z 𝒦 ℐ :=
  mapBifunctorTotalMap_naturality_functor (sheafTensor X.sheaf)
    (curriedTensor (ModuleCat.{u} (baseRing X))) (sectionsTensor W)
    (fun f b => sectionsTensor_naturality_left (G := b) W f)
    (fun a {b b'} g => sectionsTensor_naturality_right (F := a) (G := b) (G' := b') W g)
    (sectionsTensor Z)
    (fun f b => sectionsTensor_naturality_left (G := b) Z f)
    (fun a {b b'} g => sectionsTensor_naturality_right (F := a) (G := b) (G' := b') Z g)
    (openRestriction h)
    (fun a b =>
      ((sectionsTensor_restriction (F := a) (G := b) W h).trans
        (congrArg (fun z => z ≫ sectionsTensor Z a b)
          (MonoidalCategory.tensorHom_def ((openRestriction h).app a)
            ((openRestriction h).app b)))).symm)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) 𝒦 ℐ

end Total

/-! ### Composition of maps of total complexes of a bifunctor -/

section MapComp

universe v₁ v₂ vd uu₁ uu₂ ud

variable {C₁ : Type uu₁} {C₂ : Type uu₂} {D : Type ud} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{vd} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (Eb : C₁ ⥤ C₂ ⥤ D) [Eb.PreservesZeroMorphisms] [∀ a, (Eb.obj a).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c : ComplexShape J)
  [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  {K₁ L₁ M₁ : HomologicalComplex C₁ c₁} {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
  (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂)
  [HomologicalComplex.HasMapBifunctor K₁ K₂ Eb c]
  [HomologicalComplex.HasMapBifunctor L₁ L₂ Eb c]
  [HomologicalComplex.HasMapBifunctor M₁ M₂ Eb c]

/-- Two maps of a bifunctor, in each variable in turn, compose to the map of the composites. -/
theorem bifunctor_app_map_comp {A B G : Type*} [Category A] [Category B] [Category G]
    (Eb' : A ⥤ B ⥤ G) {a a' a'' : A} {b b' b'' : B}
    (f₁ : a ⟶ a') (g₁ : a' ⟶ a'') (f₂ : b ⟶ b') (g₂ : b' ⟶ b'') :
    ((Eb'.map f₁).app b ≫ (Eb'.obj a').map f₂) ≫
        ((Eb'.map g₁).app b' ≫ (Eb'.obj a'').map g₂) =
      (Eb'.map (f₁ ≫ g₁)).app b ≫ (Eb'.obj a'').map (f₂ ≫ g₂) := by
  have hn := (Eb'.map g₁).naturality f₂
  simp only [Eb'.map_comp, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

/-- Maps of total complexes of a bifunctor compose componentwise. -/
theorem mapBifunctorMap_comp :
    HomologicalComplex.mapBifunctorMap f₁ f₂ Eb c ≫
        HomologicalComplex.mapBifunctorMap g₁ g₂ Eb c =
      HomologicalComplex.mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) Eb c := by
  change HomologicalComplex₂.total.map _ c ≫ HomologicalComplex₂.total.map _ c =
    HomologicalComplex₂.total.map _ c
  rw [← HomologicalComplex₂.total.map_comp,
    bifunctor_app_map_comp (Eb.mapBifunctorHomologicalComplex c₁ c₂) f₁ g₁ f₂ g₂]

end MapComp

/-! ### A choice of resolutions -/

section CupData

variable (X : RingedSpace.{u, u})

/-- **A choice of resolutions for the cup product at an arbitrary open.**

For complexes `K` and `M` of `𝒪_X`-modules this records: a K-flat complex `T` of flat
`A`-modules together with a map `T ⟶ Γ(X, 𝒦)` exhibiting it as a representative of
`RΓ(X, K)`; a K-flat complex `𝒦` of flat `𝒪_X`-modules resolving `K`, together with a
K-injective resolution of `𝒦` against which `T` is measured; a K-injective complex `ℐ` with
injective terms resolving `M`; and a quasi-isomorphism `Tot(𝒦 ⊗_{𝒪_X} ℐ) ⟶ 𝒥` into a
K-injective complex with injective terms.

Every field is a complex, a resolution or a quasi-isomorphism: `T`, `𝒦`, `ℐ`, `ℰ` and `𝒥` are
complexes constrained by K-flatness, flatness of the terms, K-injectivity and injectivity of
the terms, and `cplxRes`, `cplxToKinj`, `injRes`, `toTgt` and `toSections` are maps of complexes
constrained to be quasi-isomorphisms.  Nothing here is a cup product, a tensor comparison, a
connecting map or a distinguished triangle: the cup product is `CupData.cupMap` below, which is
constructed from this data. -/
structure CupData (K M : CochainComplex (Modules X) ℤ) where
  /-- A complex of `A`-modules. -/
  T : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ
  /-- `T` is K-flat. -/
  T_kFlat : T.KFlat
  /-- The terms of `T` are flat `A`-modules. -/
  T_flat : ∀ i : ℤ, Module.Flat (baseRing X) (T.X i)
  /-- A complex of `𝒪_X`-modules. -/
  cplx : CochainComplex (Modules X) ℤ
  /-- `𝒦` is K-flat. -/
  cplx_kFlat : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X cplx
  /-- The terms of `𝒦` are flat `𝒪_X`-modules. -/
  cplx_flat : ∀ i : ℤ,
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (cplx.X i)
  /-- `𝒦` resolves `K`. -/
  cplxRes : cplx ⟶ K
  /-- The resolution of `K` by `𝒦` is a quasi-isomorphism. -/
  cplxRes_quasiIso : QuasiIso cplxRes
  /-- A K-injective complex receiving `𝒦`, against which the sections of `𝒦` are measured. -/
  kinj : CochainComplex (Modules X) ℤ
  /-- `ℰ` is K-injective. -/
  kinj_kInjective : kinj.IsKInjective
  /-- The terms of `ℰ` are injective `𝒪_X`-modules. -/
  kinj_injective : ∀ i : ℤ, Injective (kinj.X i)
  /-- `ℰ` resolves `𝒦`. -/
  cplxToKinj : cplx ⟶ kinj
  /-- The resolution of `𝒦` by `ℰ` is a quasi-isomorphism. -/
  cplxToKinj_quasiIso : QuasiIso cplxToKinj
  /-- The map `T ⟶ Γ(X, 𝒦)`, adjoint to a map `T ⊗_A 𝒪_X ⟶ 𝒦` of complexes of
  `𝒪_X`-modules. -/
  toSections : T ⟶ ((openSections X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj cplx
  /-- `T` represents `RΓ(X, K)` through `toSections`: composed with the sections of a
  K-injective resolution of `𝒦` it is a quasi-isomorphism. -/
  toSections_quasiIso : QuasiIso (toSections ≫
    ((openSections X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map cplxToKinj)
  /-- A complex of `𝒪_X`-modules. -/
  inj : CochainComplex (Modules X) ℤ
  /-- `ℐ` is K-injective. -/
  inj_kInjective : inj.IsKInjective
  /-- The terms of `ℐ` are injective `𝒪_X`-modules. -/
  inj_injective : ∀ i : ℤ, Injective (inj.X i)
  /-- `ℐ` resolves `M`. -/
  injRes : M ⟶ inj
  /-- The resolution of `M` by `ℐ` is a quasi-isomorphism. -/
  injRes_quasiIso : QuasiIso injRes
  /-- A complex of `𝒪_X`-modules. -/
  tgt : CochainComplex (Modules X) ℤ
  /-- `𝒥` is K-injective. -/
  tgt_kInjective : tgt.IsKInjective
  /-- The terms of `𝒥` are injective `𝒪_X`-modules. -/
  tgt_injective : ∀ i : ℤ, Injective (tgt.X i)
  /-- The map `Tot(𝒦 ⊗_{𝒪_X} ℐ) ⟶ 𝒥`. -/
  toTgt : HomologicalComplex.mapBifunctor cplx inj (sheafTensor X.sheaf) (ComplexShape.up ℤ) ⟶ tgt
  /-- `𝒥` resolves `Tot(𝒦 ⊗_{𝒪_X} ℐ)`. -/
  toTgt_quasiIso : QuasiIso toTgt

variable {X} {K M : CochainComplex (Modules X) ℤ}

/-- The map `T ⟶ Γ(W, 𝒦)` obtained from `T ⟶ Γ(X, 𝒦)` by restriction to `W`. -/
def CupData.toSectionsOver (d : CupData X K M) (W : Opens X.carrier) :
    d.T ⟶ ((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj d.cplx :=
  d.toSections ≫
    (NatTrans.mapHomologicalComplex (openRestriction (le_top : W ≤ ⊤))
      (ComplexShape.up ℤ)).app d.cplx

/-- Restricting the map `T ⟶ Γ(W, 𝒦)` to a smaller open gives the map for that open. -/
theorem CupData.toSectionsOver_restriction (d : CupData X K M) {Z W : Opens X.carrier}
    (h : Z ≤ W) :
    d.toSectionsOver W ≫
        (NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app d.cplx =
      d.toSectionsOver Z := by
  rw [CupData.toSectionsOver, CupData.toSectionsOver, Category.assoc, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp]
  exact congrArg (fun z => d.toSections ≫
    (NatTrans.mapHomologicalComplex z (ComplexShape.up ℤ)).app d.cplx)
    (Stacks.Cohomology.LinearDerivedSections.linearRestriction_comp X h (le_top : W ≤ ⊤))

/-- **The `A`-linear cup product at an open `W`**, as a map of complexes of `A`-modules

`Tot(T ⊗_A Γ(W, ℐ)) ⟶ Γ(W, 𝒥)`.

It is the map `T ⟶ Γ(W, 𝒦)` in the first tensor factor, followed by the comparison
`Tot(Γ(W, 𝒦) ⊗_A Γ(W, ℐ)) ⟶ Γ(W, Tot(𝒦 ⊗_{𝒪_X} ℐ))` and the sections over `W` of
`Tot(𝒦 ⊗_{𝒪_X} ℐ) ⟶ 𝒥`. -/
def CupData.cupMap (d : CupData X K M) (W : Opens X.carrier) :
    HomologicalComplex.mapBifunctor d.T
        (((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj d.inj)
        (curriedTensor (ModuleCat.{u} (baseRing X))) (ComplexShape.up ℤ) ⟶
      ((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj d.tgt :=
  HomologicalComplex.mapBifunctorMap (d.toSectionsOver W)
      (𝟙 (((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj d.inj))
      (curriedTensor (ModuleCat.{u} (baseRing X))) (ComplexShape.up ℤ) ≫
    sectionsTensorTotal X W d.cplx d.inj ≫
      ((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).map d.toTgt

/-- **The cup products at the various opens are compatible with restriction, on the nose.**  One
choice of resolutions gives the map for every open at once, and the maps are induced by
evaluating fixed maps of complexes of sheaves on sections. -/
theorem CupData.cupMap_restriction (d : CupData X K M) {Z W : Opens X.carrier} (h : Z ≤ W) :
    d.cupMap W ≫
        (NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app d.tgt =
      HomologicalComplex.mapBifunctorMap (𝟙 d.T)
          ((NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app d.inj)
          (curriedTensor (ModuleCat.{u} (baseRing X))) (ComplexShape.up ℤ) ≫
        d.cupMap Z := by
  dsimp only [CupData.cupMap]
  simp only [Category.assoc]
  rw [(NatTrans.mapHomologicalComplex (openRestriction h)
      (ComplexShape.up ℤ)).naturality d.toTgt,
    reassoc_of% (sectionsTensorTotal_restriction X h d.cplx d.inj),
    reassoc_of% mapBifunctorMap_comp, reassoc_of% mapBifunctorMap_comp,
    Category.id_comp, Category.comp_id, Category.id_comp,
    d.toSectionsOver_restriction h]

end CupData

end Stacks.Cohomology.LinearCupProductFamily

end
