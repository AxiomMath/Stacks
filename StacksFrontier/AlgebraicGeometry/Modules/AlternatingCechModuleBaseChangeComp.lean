module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor

/-!
# The cocycle identity for the Čech base-change comparison

Let `φ : A →+* A'` and `ψ : A' →+* A''` be ring maps, let `f : X ⟶ Spec A` be a separated
morphism, and let `IsPullback g f' f (Spec φ)` and `IsPullback g' f'' f' (Spec ψ)` be two
cartesian squares, so that `X'` is the base change of `X` along `Spec A' → Spec A` and `X''` the
base change of `X'` along `Spec A'' → Spec A'`. For a quasi-coherent `𝒪_X`-module `F`, a finite
family `U : I → X.Opens` of affine opens and the inverse-image families `U'` on `X'` and `U''`
on `X''`, `StacksFrontier/AlgebraicGeometry/Modules/AlternatingCechModuleBaseChange.lean` provides
a base-change isomorphism of alternating Čech complexes for each of `φ`, `ψ` and `ψ ∘ φ`. This
file proves that the comparison for the composite *is* the composite of the two comparisons.

This is the cocycle identity named as missing in the module docstring of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsUniversalModelData.lean`, one of
the three ingredients a naturality square in `A'` for [Stacks, Tag 07VL] needs.

Both sides are morphisms of `CochainComplex (ModuleCat A'') ℕ` out of the twofold extension of
scalars `(Č_alt(U, F) ⊗_A A') ⊗_{A'} A''`, so two further identifications enter the square: the
composition isomorphism `(- ⊗_A A') ⊗_{A'} A'' ≅ - ⊗_A A''` of extension of scalars, and the
identification of the Čech complex of `g'^*(g^*F)` with that of `(g' ≫ g)^*F`. The latter comes
from `AlgebraicGeometry.Scheme.Modules.pullbackComp` together with the functoriality of the
alternating Čech complex of `A`-modules in the module, which is built here.

## Main definitions

* `Stacks.Cech.cochainModuleMapₗ`, `Stacks.Cech.alternatingCochainModuleMapₗ` and
  `Stacks.Cech.alternatingCechModuleObjMap`: a morphism of `𝒪_X`-modules acting on Čech
  cochains, on alternating Čech cochains and degreewise on the alternating Čech modules, each
  linearly over the base ring.
* `Stacks.Cech.alternatingCechModuleComplexMap` and
  `Stacks.Cech.alternatingCechModuleComplexMapIso`: the alternating Čech complex of `A`-modules
  as a functor of the module, and the isomorphism of complexes induced by an isomorphism of
  modules.
* `Stacks.Cech.extendScalarsComplexNatCompIso`: the composition isomorphism
  `(- ⊗_A A') ⊗_{A'} A'' ≅ - ⊗_A A''` on `ℕ`-indexed cochain complexes. The `ℤ`-indexed
  counterpart is
  `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplexCompIso`; both are
  `ModuleCat.extendScalarsComp` read through
  `CategoryTheory.Functor.mapHomologicalComplexCompIso`.

## Main results

* `Stacks.Cech.pullbackSections_comp`: **the canonical comparison on sections is a cocycle** —
  pulling a section back along `g` and then along `g'` is pulling it back along `g' ≫ g`. This
  is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` in the spelling that the Čech
  comparison uses.
* `Stacks.Cech.cochainBaseChange_comp`: the same statement for Čech cochains.
* `Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comp` and
  `Stacks.Cech.alternatingCechModuleComplexBaseChangeIso_comp`: **the cocycle identity for the
  base-change comparison**, in each degree and for the complexes.
* `Stacks.Cech.alternatingCechModuleComplexBaseChangeIso_comp_of_isPullback`: the same identity
  with every derived datum produced from the two cartesian squares alone.
* `Stacks.Cech.isPullback_comp_specMap`: the two squares paste to a cartesian square over
  `Spec (ψ ∘ φ)`, and `Stacks.Cech.isAffineOpen_preimage_family`: the inverse-image family of a
  family of affine opens is a family of affine opens.
* `Stacks.Cech.extendScalarsComp_inv_app_one_one_tmul` and
  `Stacks.Cech.extendScalars_hom_ext_one_one_tmul`: the composition isomorphism for extension of
  scalars carries `1 ⊗ (1 ⊗ m)` to `1 ⊗ m`, and a morphism out of a twofold extension of scalars
  is determined by its values on the elements `1 ⊗ (1 ⊗ s)`.

## Implementation notes

**The whole content is the cocycle identity for the unit of `f^* ⊣ f_*`.** The degreewise
base-change isomorphism is pinned on `1 ⊗ s` by
`Stacks.Cech.alternatingCechModuleObjBaseChangeIso_hom_one_tmul`, and its value there is the
comparison of alternating Čech cochains, which is "unit of the adjunction at an intersection,
then restrict". So once `Stacks.Cech.extendScalars_hom_ext_one_one_tmul` and
`HomologicalComplex.hom_ext` have reduced the square to elements, nothing is left but
`AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` applied in each tuple of indices. No
part of the argument re-examines quasi-coherence, affineness or the cartesian squares: those
enter only through the three isomorphisms being compared.

**The index reindexing is the identity.** `Stacks.Cech.alternatingCechModuleComplexBaseChangeIso`
admits an arbitrary equivalence `e : I' ≃ I` of index types; here all three families are indexed
by the same `I` and `e` is `Equiv.refl I` throughout. Generality in `e` would make the two sides
of the square comparable only after a further reindexing identification, and buys nothing.

**Where term position is forced.** Two steps refuse to be done by rewriting, both because the
`Module` instance reached through `ModuleCat.restrictScalars` is only definitionally the one the
`⊗ₜ[R, f]` notation builds. `rw [← ModuleCat.extendScalarsComp_hom_app_one_tmul]` reports
"pattern not found" with an application type mismatch about that instance underneath, so
`Stacks.Cech.extendScalarsComp_inv_app_one_one_tmul` does the step with `congrArg`; and
`simp only [CategoryTheory.comp_apply]` does not fire on a composite sitting inside
`ConcreteCategory.hom`, so the degreewise proof splits the two composites with
`CategoryTheory.comp_apply` in term position through `Eq.trans`. The two `..._hom_one_tmul`
normalisations are likewise consumed by `Eq.trans`/`congrArg`, as in the imported base-change
file.

**No `@[stacks]` attribute.** Stacks 01FH already carries the two Čech complexes and their
inclusion, and Stacks 01XL — the computation of `Rf_*F` by this complex — is not proved here.
The content is the auxiliary coherence of the extension-of-scalars comparison of the imported
file, which that computation's functoriality in the base ring consumes; it is not a clause of
either tag.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.Cech

/-! ### Functoriality of the alternating Čech complex in the module -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) {G H K : X.Modules}

/-- A morphism of `𝒪_X`-modules acting on Čech cochains, as a map linear over the base
ring. -/
def cochainModuleMapₗ (t : G ⟶ H) (p : ℕ) :
    letI := cochainModule f U G p
    letI := cochainModule f U H p
    CechCochains.Cochain U G.presheaf p →ₗ[A] CechCochains.Cochain U H.presheaf p :=
  letI := cochainModule f U G p
  letI := cochainModule f U H p
  { toFun := cochainMap U t.mapPresheaf p
    map_add' := map_add (cochainMap U t.mapPresheaf p)
    map_smul' := fun a s ↦ by
      funext i
      change t.app (CechCochains.inter U i) ((a • s) i) =
        (baseRingHom f (CechCochains.inter U i)).hom a •
          t.app (CechCochains.inter U i) (s i)
      rw [cochain_smul_apply, Scheme.Modules.Hom.app_smul] }

/-- The comparison of `Stacks.Cech.cochainModuleMapₗ` applies the morphism of modules to the
section attached to each tuple. -/
theorem cochainModuleMapₗ_apply (t : G ⟶ H) (p : ℕ)
    (s : CechCochains.Cochain U G.presheaf p) (i : Fin (p + 1) → I) :
    cochainModuleMapₗ f U t p s i = t.app (CechCochains.inter U i) (s i) := rfl

/-- A morphism of `𝒪_X`-modules acting on alternating Čech cochains, as a map linear over the
base ring. -/
def alternatingCochainModuleMapₗ (t : G ⟶ H) (p : ℕ) :
    letI := cochainModule f U G p
    letI := cochainModule f U H p
    alternatingSubmodule f U G p →ₗ[A] alternatingSubmodule f U H p :=
  letI := cochainModule f U G p
  letI := cochainModule f U H p
  (cochainModuleMapₗ f U t p).restrict
    (fun _ hs ↦ cochainMap_isAlternating U t.mapPresheaf p hs)

/-- The degreewise morphism of alternating Čech modules induced by a morphism of
`𝒪_X`-modules. -/
def alternatingCechModuleObjMap (t : G ⟶ H) (p : ℕ) :
    alternatingCechModuleObj f U G p ⟶ alternatingCechModuleObj f U H p :=
  letI := cochainModule f U G p
  letI := cochainModule f U H p
  ModuleCat.ofHom (alternatingCochainModuleMapₗ f U t p)

/-- The degreewise morphism applies the morphism of modules to the section attached to each
tuple. -/
theorem alternatingCechModuleObjMap_apply (t : G ⟶ H) (p : ℕ)
    (s : alternatingCechModuleObj f U G p) (i : Fin (p + 1) → I) :
    (alternatingCechModuleObjMap f U t p s).1 i = t.app (CechCochains.inter U i) (s.1 i) := rfl

/-- **The alternating Čech complex of `A`-modules is functorial in the module.** -/
def alternatingCechModuleComplexMap (t : G ⟶ H) :
    alternatingCechModuleComplex f U G ⟶ alternatingCechModuleComplex f U H :=
  CochainComplex.ofHom (fun p ↦ alternatingCechModuleObjMap f U t p) (fun p ↦ by
    rw [alternatingCechModuleComplex_d, alternatingCechModuleComplex_d]
    ext s
    exact Subtype.ext (cochainMap_cechD U t.mapPresheaf p s.1).symm)

/-- In each degree the induced morphism of complexes is the degreewise one. -/
@[simp]
theorem alternatingCechModuleComplexMap_f (t : G ⟶ H) (p : ℕ) :
    (alternatingCechModuleComplexMap f U t).f p = alternatingCechModuleObjMap f U t p := rfl

/-- The identity morphism of modules induces the identity morphism of complexes. -/
theorem alternatingCechModuleComplexMap_id (G : X.Modules) :
    alternatingCechModuleComplexMap f U (𝟙 G) = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  ext s
  exact Subtype.ext (funext fun _ ↦ rfl)

/-- The induced morphisms of complexes compose. -/
theorem alternatingCechModuleComplexMap_comp (t : G ⟶ H) (t' : H ⟶ K) :
    alternatingCechModuleComplexMap f U (t ≫ t') =
      alternatingCechModuleComplexMap f U t ≫ alternatingCechModuleComplexMap f U t' := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  ext s
  exact Subtype.ext (funext fun _ ↦ rfl)

/-- **An isomorphism of `𝒪_X`-modules induces an isomorphism of alternating Čech complexes of
`A`-modules.** -/
def alternatingCechModuleComplexMapIso (t : G ≅ H) :
    alternatingCechModuleComplex f U G ≅ alternatingCechModuleComplex f U H where
  hom := alternatingCechModuleComplexMap f U t.hom
  inv := alternatingCechModuleComplexMap f U t.inv
  hom_inv_id := by
    rw [← alternatingCechModuleComplexMap_comp, t.hom_inv_id,
      alternatingCechModuleComplexMap_id]
  inv_hom_id := by
    rw [← alternatingCechModuleComplexMap_comp, t.inv_hom_id,
      alternatingCechModuleComplexMap_id]

/-! ### Extension of scalars along a composite of ring maps -/

section ExtendScalars

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  (φ : A →+* A') (ψ : A' →+* A'')

/-- **Termwise extension of scalars composes**, as functors on `ℕ`-indexed cochain complexes:
`(- ⊗_A A') ⊗_{A'} A'' ≅ - ⊗_A A''`. -/
def extendScalarsComplexNatCompIso :
    (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)).mapHomologicalComplex
        (ComplexShape.up ℕ) :=
  Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℕ)

/-- `ModuleCat.extendScalarsComp` read backwards on the canonical generators: its inverse
carries `1 ⊗ (1 ⊗ m)` to `1 ⊗ m`. -/
theorem extendScalarsComp_inv_app_one_one_tmul (M : ModuleCat.{u} A) (m : M) :
    (ModuleCat.extendScalarsComp φ ψ).inv.app M
        ((1 : A'') ⊗ₜ[A', ψ] ((1 : A') ⊗ₜ[A, φ] m)) = (1 : A'') ⊗ₜ[A, ψ.comp φ] m := by
  have hid : ∀ x, (ModuleCat.extendScalarsComp φ ψ).inv.app M
      ((ModuleCat.extendScalarsComp φ ψ).hom.app M x) = x := fun x ↦ by
    rw [← CategoryTheory.comp_apply, Iso.hom_inv_id_app, CategoryTheory.id_apply]
  exact (congrArg (fun x ↦ (ModuleCat.extendScalarsComp φ ψ).inv.app M x)
    (ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ M m)).symm.trans
    (hid ((1 : A'') ⊗ₜ[A, ψ.comp φ] m))

/-- Two morphisms out of a twofold extension of scalars agree as soon as they agree on the
elements `1 ⊗ (1 ⊗ s)`. This is `ModuleCat.ExtendScalars.hom_ext` applied twice, through the
adjunction that turns a morphism out of `A'' ⊗_{A'} -` into one into the restriction of
scalars along `ψ`. -/
theorem extendScalars_hom_ext_one_one_tmul {M : ModuleCat.{u} A} {N : ModuleCat.{u} A''}
    {α β : (ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M) ⟶ N}
    (h : ∀ s : M, α ((1 : A'') ⊗ₜ[A', ψ] ((1 : A') ⊗ₜ[A, φ] s)) =
      β ((1 : A'') ⊗ₜ[A', ψ] ((1 : A') ⊗ₜ[A, φ] s))) : α = β :=
  ((ModuleCat.extendRestrictScalarsAdj ψ).homEquiv
    ((ModuleCat.extendScalars φ).obj M) N).injective (ModuleCat.ExtendScalars.hom_ext h)

end ExtendScalars

/-! ### The cocycle identity on sections and on Čech cochains -/

section Cocycle

variable {X X' X'' : Scheme.{u}} (g : X' ⟶ X) (g' : X'' ⟶ X') (F : X.Modules)

/-- **The canonical comparison on sections is a cocycle.** Pulling a section back along `g` and
then along `g'` is pulling it back along `g' ≫ g`, read through
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem pullbackSections_comp {W : X.Opens} {V : X'.Opens} {T : X''.Opens}
    (hV : V ≤ g ⁻¹ᵁ W) (hT : T ≤ g' ⁻¹ᵁ V) (hTW : T ≤ (g' ≫ g) ⁻¹ᵁ W) (a : Γ(F, W)) :
    ((Scheme.Modules.pullbackComp g' g).hom.app F).app T
        (CechCochains.restr
          ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback g).obj F)).presheaf hT
          (pullbackSections g' ((Scheme.Modules.pullback g).obj F) V
            (CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf hV
              (pullbackSections g F W a)))) =
      CechCochains.restr ((Scheme.Modules.pullback (g' ≫ g)).obj F).presheaf hTW
        (pullbackSections (g' ≫ g) F W a) :=
  Scheme.Modules.pullbackSection_comp g' g F W V T hV hT hTW a

variable {I : Type u} (U : I → X.Opens) (U' : I → X'.Opens) (U'' : I → X''.Opens)
  (hU' : ∀ i, U' i = g ⁻¹ᵁ U i) (hU'' : ∀ i, U'' i = g' ⁻¹ᵁ U' i)

include hU' hU'' in
/-- The inverse-image family of an inverse-image family is the inverse-image family of the
composite. -/
theorem preimage_trans (i : I) : U'' i = (g' ≫ g) ⁻¹ᵁ U i := by
  rw [hU'' i, hU' i, Scheme.Hom.comp_preimage]

/-- **The comparison on Čech cochains is a cocycle**: comparing along `g` and then along `g'`
is comparing along `g' ≫ g`, once the two modules are identified by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem cochainBaseChange_comp (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    cochainMap U'' ((Scheme.Modules.pullbackComp g' g).hom.app F).mapPresheaf p
        (cochainBaseChange g' U' U'' (Equiv.refl I) ((Scheme.Modules.pullback g).obj F) hU'' p
          (cochainBaseChange g U U' (Equiv.refl I) F hU' p s)) =
      cochainBaseChange (g' ≫ g) U U'' (Equiv.refl I) F
        (preimage_trans g g' U U' U'' hU' hU'') p s := by
  funext i
  exact pullbackSections_comp g g' F _ _ _ (s i)

end Cocycle

/-! ### The data carried by a tower of two base changes -/

section Tower

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  {X X' X'' : Scheme.{u}}

/-- **The two cartesian squares of a tower of base changes paste**: `X''` is the base change of
`X` along `Spec` of the composite ring map. -/
theorem isPullback_comp_specMap (φ : A →+* A') (ψ : A' →+* A'')
    (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (f'' : X'' ⟶ Spec (.of A''))
    (g : X' ⟶ X) (g' : X'' ⟶ X')
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ))) :
    IsPullback (g' ≫ g) f'' f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  exact hsq'.paste_horiz hsq

/-- The inverse-image family of a family of affine opens is again a family of affine opens. -/
theorem isAffineOpen_preimage_family (φ : A →+* A') (f : X ⟶ Spec (.of A))
    (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {I : Type u} (U : I → X.Opens) (U' : I → X'.Opens) (hU' : ∀ i, U' i = g ⁻¹ᵁ U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (i : I) : IsAffineOpen (U' i) := by
  rw [hU' i]
  exact isAffineOpen_preimage_of_isPullback φ f f' g hsq (hUaff i)

end Tower

/-! ### The cocycle identity for the base-change isomorphism -/

section BaseChangeComp

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  (φ : A →+* A') (ψ : A' →+* A'')
  {X X' X'' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A'))
  (f'' : X'' ⟶ Spec (.of A'')) (g : X' ⟶ X) (g' : X'' ⟶ X') (F : X.Modules)
  {I : Type u} (U : I → X.Opens) (U' : I → X'.Opens) (U'' : I → X''.Opens)
  (hU' : ∀ i, U' i = g ⁻¹ᵁ U i) (hU'' : ∀ i, U'' i = g' ⁻¹ᵁ U' i)
  [Finite I] [IsSeparated f] [F.IsQuasicoherent]

section Data

variable (hbase : ∀ W : X.Opens,
    baseRingHom f W ≫ g.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g ⁻¹ᵁ W))
  (hbase' : ∀ W : X'.Opens,
    baseRingHom f' W ≫ g'.app W = CommRingCat.ofHom ψ ≫ baseRingHom f'' (g' ⁻¹ᵁ W))
  (hbase'' : ∀ W : X.Opens, baseRingHom f W ≫ (g' ≫ g).app W =
    CommRingCat.ofHom (ψ.comp φ) ≫ baseRingHom f'' ((g' ≫ g) ⁻¹ᵁ W))
  [IsSeparated f']
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ)))
  (hsq'' : IsPullback (g' ≫ g) f'' f (Spec.map (CommRingCat.ofHom (ψ.comp φ))))
  (hUaff : ∀ i, IsAffineOpen (U i)) (hU'aff : ∀ i, IsAffineOpen (U' i))

/-- **The degreewise cocycle identity for the Čech base-change comparison.** -/
theorem alternatingCechModuleObjBaseChangeIso_comp (p : ℕ) :
    (ModuleCat.extendScalars ψ).map
          (alternatingCechModuleObjBaseChangeIso g U U' (Equiv.refl I) F hU' φ f f' hbase hsq
            hUaff p).hom ≫
        (alternatingCechModuleObjBaseChangeIso g' U' U'' (Equiv.refl I)
            ((Scheme.Modules.pullback g).obj F) hU'' ψ f' f'' hbase' hsq' hU'aff p).hom ≫
        alternatingCechModuleObjMap f'' U''
          ((Scheme.Modules.pullbackComp g' g).hom.app F) p =
      (ModuleCat.extendScalarsComp φ ψ).inv.app (alternatingCechModuleObj f U F p) ≫
        (alternatingCechModuleObjBaseChangeIso (g' ≫ g) U U'' (Equiv.refl I) F
          (preimage_trans g g' U U' U'' hU' hU'') (ψ.comp φ) f f'' hbase'' hsq'' hUaff p).hom := by
  refine extendScalars_hom_ext_one_one_tmul φ ψ fun s ↦ ?_
  have hmap : (ModuleCat.extendScalars ψ).map
        (alternatingCechModuleObjBaseChangeIso g U U' (Equiv.refl I) F hU' φ f f' hbase hsq
          hUaff p).hom ((1 : A'') ⊗ₜ[A', ψ] ((1 : A') ⊗ₜ[A, φ] s)) =
      (1 : A'') ⊗ₜ[A', ψ]
        (alternatingCochainBaseChangeₗ g U U' (Equiv.refl I) F hU' φ f f' hbase p s) :=
    (ModuleCat.ExtendScalars.map_tmul ψ _ (1 : A'') _).trans
      (congrArg (fun y ↦ (1 : A'') ⊗ₜ[A', ψ] y)
        (alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U U' (Equiv.refl I) F hU' φ f f'
          hbase hsq hUaff p s))
  have hinv : (ModuleCat.extendScalarsComp φ ψ).inv.app (alternatingCechModuleObj f U F p)
      ((1 : A'') ⊗ₜ[A', ψ] ((1 : A') ⊗ₜ[A, φ] s)) = (1 : A'') ⊗ₜ[A, ψ.comp φ] s :=
    extendScalarsComp_inv_app_one_one_tmul φ ψ _ s
  refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
  refine Eq.trans ?_ (CategoryTheory.comp_apply _ _ _).symm
  rw [hmap, hinv]
  refine Eq.trans (congrArg (fun y ↦ alternatingCechModuleObjMap f'' U''
      ((Scheme.Modules.pullbackComp g' g).hom.app F) p y)
    (alternatingCechModuleObjBaseChangeIso_hom_one_tmul g' U' U'' (Equiv.refl I)
      ((Scheme.Modules.pullback g).obj F) hU'' ψ f' f'' hbase' hsq' hU'aff p _)) ?_
  refine Eq.trans ?_ (alternatingCechModuleObjBaseChangeIso_hom_one_tmul (g' ≫ g) U U''
    (Equiv.refl I) F (preimage_trans g g' U U' U'' hU' hU'') (ψ.comp φ) f f'' hbase'' hsq''
    hUaff p s).symm
  exact Subtype.ext (cochainBaseChange_comp g g' F U U' U'' hU' hU'' p s.1)

/-- **The cocycle identity for the Čech base-change comparison.** Extending the scalars along
`ψ` of the comparison for `φ` and `g`, following it by the comparison for `ψ` and `g'` and then
identifying the Čech complex of `g'^*(g^*F)` with that of `(g' ≫ g)^*F` gives the comparison for
`ψ ∘ φ` and `g' ≫ g`, read through the composition isomorphism
`(- ⊗_A A') ⊗_{A'} A'' ≅ - ⊗_A A''` of
`Stacks.Cech.extendScalarsComplexNatCompIso`. -/
theorem alternatingCechModuleComplexBaseChangeIso_comp :
    ((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (alternatingCechModuleComplexBaseChangeIso g U U' (Equiv.refl I) F hU' φ f f' hbase
            hsq hUaff).hom ≫
        (alternatingCechModuleComplexBaseChangeIso g' U' U'' (Equiv.refl I)
            ((Scheme.Modules.pullback g).obj F) hU'' ψ f' f'' hbase' hsq' hU'aff).hom ≫
        (alternatingCechModuleComplexMapIso f'' U''
          ((Scheme.Modules.pullbackComp g' g).app F)).hom =
      (extendScalarsComplexNatCompIso φ ψ).hom.app (alternatingCechModuleComplex f U F) ≫
        (alternatingCechModuleComplexBaseChangeIso (g' ≫ g) U U'' (Equiv.refl I) F
          (preimage_trans g g' U U' U'' hU' hU'') (ψ.comp φ) f f'' hbase'' hsq'' hUaff).hom :=
  HomologicalComplex.hom_ext _ _ fun p ↦
    alternatingCechModuleObjBaseChangeIso_comp φ ψ f f' f'' g g' F U U' U'' hU' hU''
      hbase hbase' hbase'' hsq hsq' hsq'' hUaff hU'aff p

end Data

/-- **The cocycle identity for the Čech base-change comparison, for a tower of two cartesian
squares.** Everything the general form of
`Stacks.Cech.alternatingCechModuleComplexBaseChangeIso_comp` takes as data is produced here from
the two squares: the structural ring maps commute by
`Stacks.Cech.baseRingHom_comp_app`, the squares paste by
`Stacks.Cech.isPullback_comp_specMap`, the inverse-image family is affine by
`Stacks.Cech.isAffineOpen_preimage_family`, and `f'` is separated because separatedness is
stable under base change. -/
theorem alternatingCechModuleComplexBaseChangeIso_comp_of_isPullback
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ)))
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    haveI : IsSeparated f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq ‹IsSeparated f›
    ((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (alternatingCechModuleComplexBaseChangeIso g U U' (Equiv.refl I) F hU' φ f f'
            (fun W ↦ baseRingHom_comp_app φ f f' g hsq W) hsq hUaff).hom ≫
        (alternatingCechModuleComplexBaseChangeIso g' U' U'' (Equiv.refl I)
            ((Scheme.Modules.pullback g).obj F) hU'' ψ f' f''
            (fun W ↦ baseRingHom_comp_app ψ f' f'' g' hsq' W) hsq'
            (isAffineOpen_preimage_family φ f f' g hsq U U' hU' hUaff)).hom ≫
        (alternatingCechModuleComplexMapIso f'' U''
          ((Scheme.Modules.pullbackComp g' g).app F)).hom =
      (extendScalarsComplexNatCompIso φ ψ).hom.app (alternatingCechModuleComplex f U F) ≫
        (alternatingCechModuleComplexBaseChangeIso (g' ≫ g) U U'' (Equiv.refl I) F
          (preimage_trans g g' U U' U'' hU' hU'') (ψ.comp φ) f f''
          (fun W ↦ baseRingHom_comp_app (ψ.comp φ) f f'' (g' ≫ g)
            (isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq') W)
          (isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq') hUaff).hom := by
  have : IsSeparated f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq ‹IsSeparated f›
  exact alternatingCechModuleComplexBaseChangeIso_comp φ ψ f f' f'' g g' F U U' U'' hU' hU''
    _ _ _ hsq hsq' _ hUaff _

end BaseChangeComp

end Stacks.Cech

end
