module

public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.UniversalPushforward
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChangeDerived
public import StacksFrontier.AlgebraicGeometry.BaseChange.Hypercovering
public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.FiniteProducts
public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Scheme

/-!
# Base change of the complex of pushforwards along a hypercovering

For a cartesian square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
a simplicial object `K` of formal coproducts of opens of `X` which is finite in every simplicial
degree and all of whose members `U_i` have affine `f_i : U_i ⟶ S`, and a quasi-coherent
`𝒪_X`-module `ℱ`, the inverse image along `g` of the complex

`𝓚⁼(K, f, ℱ) = ( ∏_{i ∈ I₀} f_{i,*}ℱ|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}ℱ|_{U_i} ⟶ ⋯ )`

of `Stacks.AlgebraicGeometry.UniversalPushforward.hypercoveringPushforwardComplex` is the same
complex formed on `X'`, for the base changed simplicial object — whose members are the opens
`(g')^{-1}U_i` of `X'` — and the quasi-coherent `𝒪_{X'}`-module `(g')^*ℱ`.  This is the
hypercovering analogue of
`Stacks.AlgebraicGeometry.RelativeCechBaseChange.baseChangeRelativeCechComplexIso`, which is the
same statement for the Čech nerve of a finite affine open covering.

## Main definitions

* `baseChangeOpens`:  the base change functor `U ↦ (g')^{-1}U` on the opens of `X` over the top
  open; its image under `mapFormalCoproduct` is
  `AlgebraicGeometry.baseChangeFormalCoproduct`.
* `baseChangeOpensPullbackIso`:  the open `(g')^{-1}U` of `X'` *is* the fibre product `U ×_X X'`,
  naturally in `U`.
* `baseChangedCoefficientIso`:  the coefficients of the base changed hypercovering complex are
  the base changed coefficients of [Stacks, Tag 01XL].
* `hypercoveringComplexPullbackIso`:  the comparison of the `ℕ`-indexed complexes.

## Main results

* `baseChangeHypercoveringPushforwardComplexIso`:  **the complex of pushforwards along a
  hypercovering commutes with arbitrary base change**, as bounded below complexes of
  `𝒪_{S'}`-modules.  No hypothesis is placed on `g`, on `g'`, or on the schemes beyond the
  cartesian square.
* `baseChangeHypercoveringPushforwardComplexIso'`:  the same isomorphism with the base changed
  simplicial object written as `AlgebraicGeometry.baseChangeFormalCoproduct`, the spelling of
  [Stacks, Tag 0DAZ] that `AlgebraicGeometry.isHypercovering_baseChange` and
  `AlgebraicGeometry.isAffineOpen_baseChange_obj_left` are stated for.
* `isIso_cochainComplexFunctor_map_coefficientPullback`:  the map of `ℕ`-indexed complexes
  induced by the base change map of the coefficient presheaves is an isomorphism, because that
  map is invertible at every member of `K`.
* `relativeCechPresheaf_obj_eq`:  the coefficient presheaf of [Stacks, Tag 01XL] is the presheaf
  of monads followed by the direct image, as an equality of presheaves on `Over X`.

## Implementation notes

The proof is the one of `baseChangeRelativeCechComplexIso` with the Čech nerve of a covering
replaced by `K`:  the coefficient-level work — the base change morphism of [Stacks, Tag 02KG] and
its invertibility over an affine morphism, i.e.
`Stacks.AlgebraicGeometry.RelativeCechBaseChange.isIso_coefficientPullback_app` — does not depend
on the shape of the covering, and the only thing that changes is the functor assembling the
coefficients into a complex, from `CategoryTheory.cechComplexFunctor` to
`CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor`.

Three steps.  The inverse image passes through the complex functor by
`Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIsoOfFinite`, which asks
`g^*` to preserve only *finite* products — it is additive, and degreewise finiteness of `K` makes
that sufficient.  The resulting map of complexes is induced by the base change map of coefficient
presheaves, invertible at every member of `K` because the `f_i` are affine, so
`Stacks.CechPushforward.isIso_cochainComplexFunctor_map` makes the map of complexes invertible.
Finally the coefficients are re-indexed:  the complex of `K` with coefficients restricted along a
functor `Φ` *is* the complex of `K ⋙ mapFormalCoproduct Φ`
(`cochainComplexFunctor_mapFormalCoproduct_obj`), which turns the restriction along
`opensOverTop X` into the hypercovering complex on `Over (⊤ : Opens X)` and the restriction along
`baseChangeOpens g'` into the base changed one.

*The transports are explicit chains of equalities of functors.*  Each step is a generic `rfl`
lemma — `whiskeringRight_obj_obj`, `op_comp_eq`, `cochainComplexFunctor_mapFormalCoproduct_obj`,
`CategoryTheory.Functor.comp_obj`, `CategoryTheory.Functor.assoc` — instantiated at the scheme
data and composed with `Eq.trans` and `congrArg`.  Nothing is left to `rfl` at a composite
spelling, and no transport is inserted inside a natural transformation:  two spellings of these
presheaves differ inside `Stacks.AlgebraicGeometry.RelativeCech.relativeMonad`, and the kernel,
asked to compare the restriction maps of two of its values, does not finish.  The same is why
`Stacks.AlgebraicGeometry.RelativeCechBaseChange.qcohModule` is introduced by `congrArg` from
`iota_obj_eq_qcohModule` rather than by unification.

Two further spelling constraints have the same origin, and both are load bearing.  The opens of
`X` are written `TopologicalSpace.Opens X` and not `X.Opens`, as `hypercoveringPushforwardComplex`
writes them:  the two are definitionally equal but not identical, and the category instances of
`Over (⊤ : Opens X)` repeat the spelling often enough that unfolding it everywhere does not
finish.  And `Stacks.AlgebraicGeometry.RelativeCechBaseChange` is *not* opened here, only named:
it declares scoped high-priority instances for the products of the module categories, so opening
it would give every complex formed in this file different instance arguments from the ones
`hypercoveringPushforwardComplex` carries.  For the same reason the base changed simplicial object
is `K ⋙ mapFormalCoproduct (baseChangeOpens g')` rather than
`K ⋙ AlgebraicGeometry.baseChangeFormalCoproduct g' ⊤`, whose target category is indexed by
`g' ⁻¹ᵁ ⊤`;  the two agree (`baseChangeFormalCoproduct_comp_eq`), and
`baseChangeHypercoveringPushforwardComplexIso'` crosses that equality once, by `congrArg`, away
from the complexes.

The base change comparison of the opens is natural for free:  its target has an open immersion as
structure morphism, hence a monomorphism, and `hom_ext_of_mono` says that a hom-set of `Over X'`
with such a target has at most one element.

## References

* [Stacks Project, Tag 01XM](https://stacks.math.columbia.edu/tag/01XM)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe w u

namespace Stacks.AlgebraicGeometry.HypercoveringBaseChange

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.UniversalPushforward
open Stacks.CategoryTheory.Hypercovering

/-! ### Generic transports -/

/-- The value of `CategoryTheory.Functor.whiskeringRight` is the composition. -/
theorem whiskeringRight_obj_obj {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (W : D ⥤ E) (H : C ⥤ D) :
    ((Functor.whiskeringRight C D E).obj W).obj H = H ⋙ W := rfl

/-- The opposite of a composition of functors is the composition of the opposites. -/
theorem op_comp_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op = F.op ⋙ G.op := rfl

/-- **The complex of a simplicial formal coproduct with coefficients restricted along a functor
`Φ` is the complex of the simplicial formal coproduct pushed forward along `Φ`.**  Both have, in
degree `n`, the product over the index type of `K_n` of the values of the coefficients at the
`Φ(U_i)`, with the same restriction maps. -/
theorem cochainComplexFunctor_mapFormalCoproduct_obj {C D : Type*} [Category* C] [Category* D]
    {A : Type*} [Category* A] [HasProducts.{w} A] [Preadditive A] (Φ : D ⥤ C)
    (K : SimplicialObject (FormalCoproduct.{w} D)) (P : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cochainComplexFunctor.{w} (K ⋙ mapFormalCoproduct.{w} Φ)).obj P =
      (FormalCoproduct.cochainComplexFunctor.{w} K).obj (Φ.op ⋙ P) := rfl

/-- A hom-set of `Over Y` whose target has a monomorphism as structure morphism has at most one
element:  two such morphisms agree after composition with that monomorphism, by the triangle each
of them makes commute. -/
theorem hom_ext_of_mono {C : Type*} [Category* C] {Y : C} {A B : Over Y} [Mono B.hom]
    (p q : A ⟶ B) : p = q := by
  ext
  rw [← cancel_mono B.hom, Over.w, Over.w]

/-! ### The coefficient presheaf in the spelling of the presheaf of monads -/

variable {X X' S S' Y Z : Scheme.{u}}

/-- The underlying module of a quasi-coherent module, through the inclusion of the full
subcategory, is its underlying module. -/
theorem iota_obj_eq_qcohModule
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).obj G =
      RelativeCechBaseChange.qcohModule G :=
  rfl

/-- The coefficient presheaf of [Stacks, Tag 01XL] at a quasi-coherent module, as the value of
the functor of `Stacks.AlgebraicGeometry.CechPushforwardComplex.relativeCechPresheaf_eq`. -/
theorem relativeCechPresheaf_obj_eq_aux (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    (relativeCechPresheaf k).obj G =
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ⋙
        (relativeMonad Y).flip ⋙
          (Functor.whiskeringRight (Over Y)ᵒᵖ Y.Modules Z.Modules).obj
            (Scheme.Modules.pushforward k)).obj G :=
  congrArg (fun T ↦ T.obj G)
    (Stacks.AlgebraicGeometry.CechPushforwardComplex.relativeCechPresheaf_eq k)

/-- **The coefficient presheaf of [Stacks, Tag 01XL] is the presheaf of monads followed by the
direct image**, as an equality of presheaves on `Over Y`:  the value at `A` is `(a ≫ k)_* a^* 𝓖`
on both sides, and so is the restriction map at a morphism of `Over Y`. -/
theorem relativeCechPresheaf_obj_eq (k : Y ⟶ Z)
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    (relativeCechPresheaf k).obj G =
      (relativeMonad Y).flip.obj (RelativeCechBaseChange.qcohModule G) ⋙
        Scheme.Modules.pushforward k :=
  (relativeCechPresheaf_obj_eq_aux k G).trans
    ((Functor.comp_obj _ _ G).trans
      ((Functor.comp_obj _ _
          ((ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).obj G)).trans
        ((whiskeringRight_obj_obj _ _).trans
          (congrArg (fun M ↦ (relativeMonad Y).flip.obj M ⋙ Scheme.Modules.pushforward k)
            (iota_obj_eq_qcohModule G)))))

/-- **The coefficient presheaf of the hypercovering complex is the coefficient presheaf of
[Stacks, Tag 01XL] restricted to the opens of `X`.** -/
theorem pushforwardPresheaf_obj_eq (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pushforwardPresheaf f).obj F =
      (opensOverTop X).op ⋙
        ((relativeMonad X).flip.obj (RelativeCechBaseChange.qcohModule F) ⋙
          Scheme.Modules.pushforward f) :=
  congrArg (fun P ↦ (opensOverTop X).op ⋙ P) (relativeCechPresheaf_obj_eq f F)

/-- The inverse image of the coefficient presheaf of the hypercovering complex is the inverse
image of the coefficient presheaf of [Stacks, Tag 01XL], restricted to the opens of `X`. -/
theorem pushforwardPresheaf_comp_eq (f : X ⟶ S) (g : S' ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pushforwardPresheaf f).obj F ⋙ Scheme.Modules.pullback g =
      (opensOverTop X).op ⋙
        ((relativeCechPresheaf f).obj F ⋙ Scheme.Modules.pullback g) :=
  Functor.assoc _ _ _

/-- The underlying module of `(g')^*ℱ` is the inverse image of the underlying module of `ℱ`. -/
theorem qcohModule_pullbackQcohObj_eq (g' : X' ⟶ X)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    RelativeCechBaseChange.qcohModule (RelativeCechBaseChange.pullbackQcohObj g' F) =
      (Scheme.Modules.pullback g').obj (RelativeCechBaseChange.qcohModule F) :=
  rfl

/-- The coefficient presheaf of the hypercovering complex of `f'` at `(g')^*ℱ`, in the spelling
of the presheaf of monads of `X'` at the inverse image of the underlying module of `ℱ`. -/
theorem pushforwardPresheaf_pullbackQcohObj_obj_eq (g' : X' ⟶ X) (f' : X' ⟶ S')
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pushforwardPresheaf f').obj (RelativeCechBaseChange.pullbackQcohObj g' F) =
      (opensOverTop X').op ⋙
        ((relativeMonad X').flip.obj
            ((Scheme.Modules.pullback g').obj (RelativeCechBaseChange.qcohModule F)) ⋙
          Scheme.Modules.pushforward f') :=
  (pushforwardPresheaf_obj_eq f' (RelativeCechBaseChange.pullbackQcohObj g' F)).trans
    (congrArg (fun M ↦ (opensOverTop X').op ⋙
      ((relativeMonad X').flip.obj M ⋙ Scheme.Modules.pushforward f'))
      (qcohModule_pullbackQcohObj_eq g' F))

/-! ### Base change of the opens of `X` -/

/-- **The base change functor on the opens of `X` over the top open:** an open `U` of `X` goes to
the open `(g')^{-1}U` of `X'`.  Its image under `mapFormalCoproduct` is
`AlgebraicGeometry.baseChangeFormalCoproduct`, the base change of a simplicial formal
coproduct. -/
noncomputable def baseChangeOpens (g' : X' ⟶ X) :
    Over (⊤ : Opens X) ⥤ Over (⊤ : Opens X') :=
  Over.post (Opens.map g'.base) (X := (⊤ : Opens X))

/-- The base change of a simplicial formal coproduct of opens is the image of `baseChangeOpens`
under `mapFormalCoproduct`. -/
theorem baseChangeFormalCoproduct_eq (g' : X' ⟶ X) :
    AlgebraicGeometry.baseChangeFormalCoproduct.{u} g' (⊤ : Opens X) =
      mapFormalCoproduct.{u} (baseChangeOpens g') :=
  rfl

/-- **The base change of a simplicial formal coproduct of opens of `X`, `K' = (g')^{-1}K`, is the
image of `K` under `mapFormalCoproduct (baseChangeOpens g')`**:  the two spellings of the base
changed simplicial object agree. -/
theorem baseChangeFormalCoproduct_comp_eq (g' : X' ⟶ X)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) :
    K ⋙ AlgebraicGeometry.baseChangeFormalCoproduct.{u} g' (⊤ : Opens X) =
      K ⋙ mapFormalCoproduct.{u} (baseChangeOpens g') :=
  rfl

/-- **The open `(g')^{-1}U` of `X'` is the fibre product `U ×_X X'`**, naturally in the open `U`
of `X`:  the square `(g')^{-1}U ⟶ U`, `(g')^{-1}U ⟶ X'` over `U ⟶ X`, `X' ⟶ X` is cartesian
(`AlgebraicGeometry.isPullback_morphismRestrict`).  Naturality is automatic:  the structure
morphism of the target is an open immersion, hence a monomorphism. -/
noncomputable def baseChangeOpensPullbackIso (g' : X' ⟶ X) :
    opensOverTop X ⋙ Over.pullback g' ≅ baseChangeOpens g' ⋙ opensOverTop X' :=
  NatIso.ofComponents
    (fun A ↦ (Over.isoMk (isPullback_morphismRestrict g' A.left).isoPullback
      (IsPullback.isoPullback_hom_snd _)).symm)
    (fun {_ B} _ ↦ by
      have : Mono ((baseChangeOpens g' ⋙ opensOverTop X').obj B).hom :=
        inferInstanceAs (Mono (Scheme.Opens.ι (X := X') (g' ⁻¹ᵁ B.left)))
      exact hom_ext_of_mono _ _)

/-! ### The base changed coefficients -/

variable {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- **The coefficients of the base changed hypercovering complex.**  Restricting the coefficient
presheaf of `f'` along `A ↦ A ×_X X'` and then along the opens of `X` is the same as restricting
the coefficient presheaf of the hypercovering complex of `f'` along the base change functor on
opens — the two differ by the identification of `(g')^{-1}U` with `U ×_X X'`. -/
noncomputable def baseChangedCoefficientIso (g' : X' ⟶ X) (f' : X' ⟶ S')
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (opensOverTop X).op ⋙ ((Over.pullback g').op ⋙
        ((relativeMonad X').flip.obj
            ((Scheme.Modules.pullback g').obj (RelativeCechBaseChange.qcohModule F)) ⋙
          Scheme.Modules.pushforward f')) ≅
      (baseChangeOpens g').op ⋙
        (pushforwardPresheaf f').obj (RelativeCechBaseChange.pullbackQcohObj g' F) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (eqToIso (op_comp_eq (opensOverTop X) (Over.pullback g')).symm) _ ≪≫
    Functor.isoWhiskerRight (NatIso.op (baseChangeOpensPullbackIso g')).symm _ ≪≫
    Functor.isoWhiskerRight (eqToIso (op_comp_eq (baseChangeOpens g') (opensOverTop X'))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (baseChangeOpens g').op
      (eqToIso (pushforwardPresheaf_pullbackQcohObj_obj_eq g' f' F)).symm

/-! ### The comparison of the complexes -/

/-- The inverse image of modules preserves products indexed by a finite type:  it is additive, so
it preserves finite products, and a product indexed by a finite type in an arbitrary universe is
one of those. -/
theorem preservesLimitsOfShape_discrete_pullback (g : S' ⟶ S) (J : Type u) (hJ : Finite J) :
    PreservesLimitsOfShape (Discrete J) (Scheme.Modules.pullback g) :=
  have := hJ
  have : (Scheme.Modules.pullback g).Additive := inferInstance
  inferInstance

/-- **The degreewise inverse image of the complex of a simplicial formal coproduct which is
finite in every degree is the complex of the inverse image of its coefficients.** -/
noncomputable def cochainComplexPullbackIso (g : S' ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I) (P : (Over (⊤ : Opens X))ᵒᵖ ⥤ S.Modules) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((FormalCoproduct.cochainComplexFunctor.{u} K).obj P) ≅
      (FormalCoproduct.cochainComplexFunctor.{u} K).obj (P ⋙ Scheme.Modules.pullback g) :=
  haveI : (Scheme.Modules.pullback g).Additive := inferInstance
  eqToIso (Functor.comp_obj (FormalCoproduct.cochainComplexFunctor.{u} K)
      ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)) P).symm ≪≫
    (Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIsoOfFinite
      (Scheme.Modules.pullback g) K hfin
      (fun J hJ ↦ preservesLimitsOfShape_discrete_pullback g J hJ)).app P ≪≫
    eqToIso ((Functor.comp_obj _ (FormalCoproduct.cochainComplexFunctor.{u} K) P).trans
      (congrArg (fun Q ↦ (FormalCoproduct.cochainComplexFunctor.{u} K).obj Q)
        (whiskeringRight_obj_obj (Scheme.Modules.pullback g) P)))

/-- The complex of `K` with coefficients on the opens of `X` is the complex of the simplicial
formal coproduct of those opens read in `Over X`. -/
theorem cochainComplexFunctor_opensOverTop_obj
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (P : (Over X)ᵒᵖ ⥤ S'.Modules) :
    (FormalCoproduct.cochainComplexFunctor.{u}
        (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).obj P =
      (FormalCoproduct.cochainComplexFunctor.{u} K).obj ((opensOverTop X).op ⋙ P) :=
  cochainComplexFunctor_mapFormalCoproduct_obj (opensOverTop X) K P

/-- The complex of the base changed simplicial formal coproduct is the complex of `K` with the
coefficients restricted along the base change functor on opens. -/
theorem cochainComplexFunctor_baseChange_obj (g' : X' ⟶ X)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (P : (Over (⊤ : Opens X'))ᵒᵖ ⥤ S'.Modules) :
    (FormalCoproduct.cochainComplexFunctor.{u}
        (K ⋙ mapFormalCoproduct.{u} (baseChangeOpens g'))).obj P =
      (FormalCoproduct.cochainComplexFunctor.{u} K).obj ((baseChangeOpens g').op ⋙ P) :=
  cochainComplexFunctor_mapFormalCoproduct_obj (baseChangeOpens g') K P

/-- The inverse image of the coefficients of the hypercovering complex, read on the simplicial
formal coproduct of the opens of `X` in `Over X`:  the restriction of the coefficient presheaf of
[Stacks, Tag 01XL] along `opensOverTop X` is absorbed into the simplicial object. -/
theorem cochainComplexFunctor_pullback_opensOverTop_eq (f : X ⟶ S) (g : S' ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (FormalCoproduct.cochainComplexFunctor.{u} K).obj
        ((pushforwardPresheaf f).obj F ⋙ Scheme.Modules.pullback g) =
      (FormalCoproduct.cochainComplexFunctor.{u}
          (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).obj
        ((relativeCechPresheaf f).obj F ⋙ Scheme.Modules.pullback g) :=
  (congrArg (fun Q ↦ (FormalCoproduct.cochainComplexFunctor.{u} K).obj Q)
      (pushforwardPresheaf_comp_eq f g F)).trans
    (cochainComplexFunctor_opensOverTop_obj K
      ((relativeCechPresheaf f).obj F ⋙ Scheme.Modules.pullback g)).symm

/-- The coefficients of [Stacks, Tag 01XL] in the spelling of the presheaf of monads, inside the
complex of a simplicial formal coproduct. -/
theorem cochainComplexFunctor_relativeMonad_eq (f : X ⟶ S) (g : S' ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (FormalCoproduct.cochainComplexFunctor.{u}
          (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).obj
        ((relativeCechPresheaf f).obj F ⋙ Scheme.Modules.pullback g) =
      (FormalCoproduct.cochainComplexFunctor.{u}
          (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).obj
        (((relativeMonad X).flip.obj (RelativeCechBaseChange.qcohModule F) ⋙
          Scheme.Modules.pushforward f) ⋙ Scheme.Modules.pullback g) :=
  congrArg (fun Q ↦ (FormalCoproduct.cochainComplexFunctor.{u}
      (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).obj Q)
    (congrArg (fun P ↦ P ⋙ Scheme.Modules.pullback g) (relativeCechPresheaf_obj_eq f F))

/-- **The inverse image of the coefficients of the hypercovering complex is the inverse image of
the coefficient presheaf of [Stacks, Tag 01XL]**, read on the simplicial formal coproduct of the
opens of `X` in `Over X` and in the spelling of the presheaf of monads:  this is the source of
the base change map of coefficient presheaves. -/
theorem cochainComplexFunctor_pullback_coefficients_eq (f : X ⟶ S) (g : S' ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (FormalCoproduct.cochainComplexFunctor.{u} K).obj
        ((pushforwardPresheaf f).obj F ⋙ Scheme.Modules.pullback g) =
      (FormalCoproduct.cochainComplexFunctor.{u}
          (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).obj
        (((relativeMonad X).flip.obj (RelativeCechBaseChange.qcohModule F) ⋙
          Scheme.Modules.pushforward f) ⋙ Scheme.Modules.pullback g) :=
  (cochainComplexFunctor_pullback_opensOverTop_eq f g K F).trans
    (cochainComplexFunctor_relativeMonad_eq f g K F)

/-- **The map of complexes induced by the base change map of the coefficient presheaves is an
isomorphism** when every member of `K` has affine structure morphism to `S`:  it is so in each
degree, being the product over the index type of `K_n` of the components of that map at the
members of `K_n`, each of which is the base change morphism of [Stacks, Tag 02KG] of an affine
morphism. -/
theorem isIso_cochainComplexFunctor_map_coefficientPullback (hw : IsPullback g' f' f g)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso ((FormalCoproduct.cochainComplexFunctor.{u}
      (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).map
        (RelativeCechBaseChange.coefficientPullback hw.w
          (RelativeCechBaseChange.pullbackCounit g')
          (RelativeCechBaseChange.qcohModule F))) := by
  refine Stacks.CechPushforward.isIso_cochainComplexFunctor_map.{u} _ _ (fun n i ↦ ?_)
  have : IsAffineHom
      ((((K ⋙ mapFormalCoproduct.{u} (opensOverTop X)).obj (op ⦋n⦌)).obj i).hom ≫ f) :=
    hK n i
  exact RelativeCechBaseChange.isIso_coefficientPullback_qcohModule_app hw F _

/-- **The inverse image of the `ℕ`-indexed complex of pushforwards along `K` is the complex of
pushforwards along the base changed simplicial formal coproduct.** -/
noncomputable def hypercoveringComplexPullbackIso (hw : IsPullback g' f' f g)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hK : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((FormalCoproduct.cochainComplexFunctor.{u} K).obj ((pushforwardPresheaf f).obj F)) ≅
      (FormalCoproduct.cochainComplexFunctor.{u}
          (K ⋙ mapFormalCoproduct.{u} (baseChangeOpens g'))).obj
        ((pushforwardPresheaf f').obj (RelativeCechBaseChange.pullbackQcohObj g' F)) :=
  haveI := isIso_cochainComplexFunctor_map_coefficientPullback hw K hK F
  cochainComplexPullbackIso g K hfin ((pushforwardPresheaf f).obj F) ≪≫
    eqToIso (cochainComplexFunctor_pullback_coefficients_eq f g K F) ≪≫
    asIso ((FormalCoproduct.cochainComplexFunctor.{u}
      (K ⋙ mapFormalCoproduct.{u} (opensOverTop X))).map
        (RelativeCechBaseChange.coefficientPullback hw.w
          (RelativeCechBaseChange.pullbackCounit g')
          (RelativeCechBaseChange.qcohModule F))) ≪≫
    eqToIso (cochainComplexFunctor_opensOverTop_obj K
      ((Over.pullback g').op ⋙
        ((relativeMonad X').flip.obj
            ((Scheme.Modules.pullback g').obj (RelativeCechBaseChange.qcohModule F)) ⋙
          Scheme.Modules.pushforward f'))) ≪≫
    (FormalCoproduct.cochainComplexFunctor.{u} K).mapIso
      (baseChangedCoefficientIso g' f' F) ≪≫
    eqToIso (cochainComplexFunctor_baseChange_obj g' K
      ((pushforwardPresheaf f').obj (RelativeCechBaseChange.pullbackQcohObj g' F))).symm

/-- **The complex of pushforwards along a hypercovering commutes with arbitrary base change.**
For a cartesian square
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
a simplicial object `K` of formal coproducts of opens of `X` which is finite in every simplicial
degree and all of whose members `U_i` have affine `f_i : U_i ⟶ S`, and a quasi-coherent
`𝒪_X`-module `ℱ`, there is a canonical isomorphism

`g^* 𝓚⁼(K, f, ℱ) ≅ 𝓚⁼(K', f', (g')^*ℱ)`

of bounded below complexes of `𝒪_{S'}`-modules, where `K'` is the base change of `K`, whose
members are the opens `(g')^{-1}U_i` of `X'`.

Degreewise the isomorphism is the base change morphism of [Stacks, Tag 02KG] at each member of
`K`, invertible there because `f_i` is affine and `ℱ` is quasi-coherent; the inverse image passes
through the degree-`n` product because it is additive and that product is finite.  Nothing is
assumed about `g`, about `g'`, or about the schemes. -/
noncomputable def baseChangeHypercoveringPushforwardComplexIso (hw : IsPullback g' f' f g)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hK : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pullback g).mapCochainComplexPlus.obj
        ((hypercoveringPushforwardComplex f K).obj F) ≅
      (hypercoveringPushforwardComplex f'
          (K ⋙ mapFormalCoproduct.{u} (baseChangeOpens g'))).obj
        (RelativeCechBaseChange.pullbackQcohObj g' F) :=
  (CochainComplex.Plus.fullyFaithfulι S'.Modules).preimageIso
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (eqToIso (hypercoveringPushforwardComplex_obj_obj f K F)) ≪≫
      Stacks.DerivedIndexing.mapExtendIsoSymm (Scheme.Modules.pullback g)
        ComplexShape.embeddingUpNat _ ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor S'.Modules).mapIso
        (hypercoveringComplexPullbackIso hw K hfin hK F) ≪≫
      eqToIso (hypercoveringPushforwardComplex_obj_obj f'
        (K ⋙ mapFormalCoproduct.{u} (baseChangeOpens g'))
        (RelativeCechBaseChange.pullbackQcohObj g' F)).symm)

/-- **The complex of pushforwards along a hypercovering commutes with arbitrary base change**,
with the base changed simplicial object written as
`AlgebraicGeometry.baseChangeFormalCoproduct`, the base change of [Stacks, Tag 0DAZ] — the
spelling for which `AlgebraicGeometry.isHypercovering_baseChange` says that the base change of a
hypercovering is a hypercovering and
`AlgebraicGeometry.isAffineOpen_baseChange_obj_left` that its members stay affine over an affine
`g'`. -/
noncomputable def baseChangeHypercoveringPushforwardComplexIso' (hw : IsPullback g' f' f g)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hK : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pullback g).mapCochainComplexPlus.obj
        ((hypercoveringPushforwardComplex f K).obj F) ≅
      (hypercoveringPushforwardComplex f'
          (K ⋙ AlgebraicGeometry.baseChangeFormalCoproduct.{u} g' (⊤ : Opens X))).obj
        (RelativeCechBaseChange.pullbackQcohObj g' F) :=
  baseChangeHypercoveringPushforwardComplexIso hw K hfin hK F ≪≫
    eqToIso (congrArg (fun E ↦ (hypercoveringPushforwardComplex f' E).obj
      (RelativeCechBaseChange.pullbackQcohObj g' F))
      (baseChangeFormalCoproduct_comp_eq g' K).symm)

end Stacks.AlgebraicGeometry.HypercoveringBaseChange

end
