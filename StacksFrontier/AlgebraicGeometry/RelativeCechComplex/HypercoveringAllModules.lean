module

public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.UniversalPushforward
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductLinear

/-!
# The relative hypercovering complex with arbitrary module coefficients

Let `f : X ⟶ S` be a morphism of schemes and let `K` be a simplicial object of formal coproducts
of opens of `X`.  `Stacks.AlgebraicGeometry.UniversalPushforward.hypercoveringPushforwardComplex`
builds from them the complex

`𝓚⁼(K, f, 𝓕) = ( ∏_{i ∈ I₀} f_{i,*}𝓕|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}𝓕|_{U_i} ⟶ ⋯ )`

of `𝒪_S`-modules, but only for a **quasi-coherent** `𝒪_X`-module `𝓕`:  its coefficient presheaf
is `Stacks.AlgebraicGeometry.RelativeCech.relativeCechPresheaf`, whose domain is the
quasi-coherent full subcategory.

This file removes that restriction.  The underlying presheaf of monads
`Stacks.AlgebraicGeometry.RelativeCech.relativeMonad` is defined on all of `X.Modules`, and the
restriction to the quasi-coherent subcategory happens only when `relativeCechPresheaf` whiskers
it with the inclusion of that subcategory.  Dropping the whiskering gives the same complex as a
functor of an arbitrary `𝒪_X`-module, which is what the comparison

`𝓚⁼(K, f, 𝓕) ⟶ Rf_*𝓕`

of [Stacks, Tag 01XN] needs:  that comparison is obtained from an injective resolution of `𝓕`,
and an injective `𝒪_X`-module is not quasi-coherent.

## Main definitions

* `relativeCechPresheafAll`:  the coefficient presheaf of [Stacks, Tag 01XL] on all of
  `X.Modules` — an object `A` of `Over X` with structure morphism `a` goes to the `𝒪_S`-module
  `(a ≫ f)_* a^*M`.
* `pushforwardPresheafAll`:  its restriction along `opensOverTop` to the opens of `X`.
* `hypercoveringPushforwardComplexAll`:  the `ℤ`-indexed complex `𝓚⁼(K, f, -)` as a functor of
  an arbitrary `𝒪_X`-module.

## Main results

* `relativeCechPresheafAll_obj_obj`, `pushforwardPresheafAll_obj_obj`:  the values of the two
  coefficient presheaves.
* `pushforwardPresheafAll_obj_obj_eq`:  on a quasi-coherent module the values agree with those
  of `pushforwardPresheaf`, so the complex below extends the complex of
  [Stacks, Tag 01XN].
* `hypercoveringPushforwardComplexAll_obj_X_eq`:  the degree `n` term in nonnegative degrees is
  the product `∏_{i ∈ Iₙ} f_{i,*}M|_{U_i}` of [Stacks, Tag 01XN].
* `isZero_hypercoveringPushforwardComplexAll_obj_X`:  the complex vanishes in negative degrees,
  which is the boundedness hypothesis the comparison machinery of
  `StacksDraft.DerivedSectionsComparison` asks of the complex it compares against a right
  derived functor.
* `relativeCechPresheafAll_additive`, `pushforwardPresheafAll_additive`,
  `hypercoveringPushforwardComplexAll_additive`:  all three are additive functors of the
  coefficient module, which is the other hypothesis of that machinery.

## Implementation notes

Additivity is proved from the bottom up rather than by `infer_instance` on the composite:  the
coefficient presheaves are built with `CategoryTheory.Functor.flip`, and instance search does
not see through `flip` to the additivity of the functors `(a ≫ f)_* a^*` it transposes.  The
proof is `NatTrans.ext` followed by the additivity of that composite in each component.
Additivity of `FormalCoproduct.cochainComplexFunctor` and of
`ComplexShape.embeddingUpNat.extendFunctor` is found by synthesis, the former through the
linearity instances of `StacksFrontier.CategoryTheory.Limits.FormalCoproductLinear`, which is why
that module is imported.

The identification with `hypercoveringPushforwardComplex` is stated degreewise and at the level
of the coefficient presheaves rather than as an equality of functors:  the two differ only by
the position of the whiskering with the inclusion of the quasi-coherent subcategory, so they are
definitionally equal, but checking that equality of functors exhausts the kernel's heartbeat
budget, while the degreewise statements are immediate.

## References

* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

open Stacks.AlgebraicGeometry.RelativeCech

variable {X S : Scheme.{u}}

/-! ### The coefficient presheaves on all modules -/

/-- **The coefficient presheaf of [Stacks, Tag 01XL] with arbitrary module coefficients.**  An
`𝒪_X`-module `M` goes to the presheaf on `Over X` whose value at an object `A` with structure
morphism `a` is the `𝒪_S`-module `(a ≫ f)_* a^*M`, with the canonical restriction maps.  This is
`Stacks.AlgebraicGeometry.RelativeCech.relativeCechPresheaf` with the restriction to the
quasi-coherent full subcategory removed. -/
noncomputable def relativeCechPresheafAll (f : X ⟶ S) :
    X.Modules ⥤ ((Over X)ᵒᵖ ⥤ S.Modules) :=
  (relativeMonad X ⋙ (Functor.whiskeringRight _ _ _).obj (pushforward f)).flip

/-- The value of the coefficient presheaf is the direct image of the restriction. -/
theorem relativeCechPresheafAll_obj_obj (f : X ⟶ S) (M : X.Modules) (A : Over X) :
    ((relativeCechPresheafAll f).obj M).obj (op A)
      = (pushforward (A.hom ≫ f)).obj ((Scheme.Modules.pullback A.hom).obj M) :=
  rfl

/-- On a quasi-coherent module the coefficient presheaf agrees with the one of
[Stacks, Tag 01XL]. -/
theorem relativeCechPresheafAll_obj_obj_eq (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (A : Over X) :
    ((relativeCechPresheafAll f).obj F.obj).obj (op A)
      = ((relativeCechPresheaf f).obj F).obj (op A) :=
  rfl

/-- **The coefficient presheaf on the opens of `X`, with arbitrary module coefficients.**  It is
`relativeCechPresheafAll` restricted along `opensOverTop`:  an open `U` of `X` goes to the
`𝒪_S`-module `(U.ι ≫ f)_* (U.ι)^*M`. -/
noncomputable def pushforwardPresheafAll (f : X ⟶ S) :
    X.Modules ⥤ ((Over (⊤ : Opens X))ᵒᵖ ⥤ S.Modules) :=
  relativeCechPresheafAll f ⋙
    (Functor.whiskeringLeft (Over (⊤ : Opens X))ᵒᵖ (Over X)ᵒᵖ S.Modules).obj
      (opensOverTop X).op

/-- The value of the coefficient presheaf on the opens of `X`. -/
theorem pushforwardPresheafAll_obj_obj (f : X ⟶ S) (M : X.Modules) (A : Over (⊤ : Opens X)) :
    ((pushforwardPresheafAll f).obj M).obj (op A)
      = (pushforward (Scheme.Opens.ι (X := X) A.left ≫ f)).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (X := X) A.left)).obj M) :=
  rfl

/-- On a quasi-coherent module the coefficient presheaf on the opens of `X` agrees with the one
of [Stacks, Tag 01XN]. -/
theorem pushforwardPresheafAll_obj_obj_eq (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (A : Over (⊤ : Opens X)) :
    ((pushforwardPresheafAll f).obj F.obj).obj (op A)
      = ((pushforwardPresheaf f).obj F).obj (op A) :=
  rfl

/-! ### Additivity -/

/-- **The coefficient presheaf of [Stacks, Tag 01XL] is an additive functor of the module.** -/
instance relativeCechPresheafAll_additive (f : X ⟶ S) :
    (relativeCechPresheafAll f).Additive where
  map_add := by
    -- Instance search does not see through `Functor.flip`, so this is proved componentwise:
    -- the component at `A` is the image under the additive functor `(a ≫ f)_* a^*`.
    intro M N g h
    refine NatTrans.ext (funext fun A ↦ ?_)
    exact ((Scheme.Modules.pullback A.unop.hom ⋙ pushforward A.unop.hom) ⋙
      pushforward f).map_add

/-- The coefficient presheaf on the opens of `X` is an additive functor of the module. -/
instance pushforwardPresheafAll_additive (f : X ⟶ S) :
    (pushforwardPresheafAll f).Additive := by
  dsimp only [pushforwardPresheafAll]
  infer_instance

/-! ### The complex -/

/-- **The complex of pushforwards along a hypercovering, with arbitrary module coefficients.**
For a simplicial object `K` of formal coproducts of opens of `X` this is the cochain complex of
`K` with coefficients in `pushforwardPresheafAll f`, indexed by `ℤ`:  its degree `n` term, for
`n ≥ 0`, is the product over the index type of `K_n` of the `𝒪_S`-modules `f_{i,*}M|_{U_i}`, its
differential is the alternating sum of the coface maps of `K`, and it vanishes in negative
degrees.

This is `Stacks.AlgebraicGeometry.UniversalPushforward.hypercoveringPushforwardComplex` as a
functor of an arbitrary `𝒪_X`-module instead of a quasi-coherent one. -/
noncomputable def hypercoveringPushforwardComplexAll (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) :
    X.Modules ⥤ CochainComplex S.Modules ℤ :=
  pushforwardPresheafAll f ⋙ FormalCoproduct.cochainComplexFunctor K ⋙
    ComplexShape.embeddingUpNat.extendFunctor S.Modules

/-- The complex of pushforwards along a hypercovering is an additive functor of the module. -/
instance hypercoveringPushforwardComplexAll_additive (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) :
    (hypercoveringPushforwardComplexAll f K).Additive := by
  dsimp only [hypercoveringPushforwardComplexAll]
  infer_instance

/-- The underlying `ℕ`-indexed complex, before the extension to integer degrees. -/
theorem hypercoveringPushforwardComplexAll_obj (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (M : X.Modules) :
    (hypercoveringPushforwardComplexAll f K).obj M
      = ((FormalCoproduct.cochainComplexFunctor K).obj
          ((pushforwardPresheafAll f).obj M)).extend ComplexShape.embeddingUpNat :=
  rfl

/-- **The degree `n` term of the `ℕ`-indexed complex is `∏_{i ∈ Iₙ} f_{i,*}M|_{U_i}`**, the term
of the complex of [Stacks, Tag 01XN]. -/
theorem cochainComplexFunctorAll_obj_X (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (M : X.Modules) (n : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor K).obj ((pushforwardPresheafAll f).obj M)).X n
      = ∏ᶜ (fun i : (K.obj (op ⦋n⦌)).I ↦
          ((pushforwardPresheafAll f).obj M).obj (op ((K.obj (op ⦋n⦌)).obj i))) :=
  rfl

/-- **The degree `n` term of the complex, in nonnegative degrees**, is the product over the index
type of `K_n` of the `𝒪_S`-modules `f_{i,*}M|_{U_i}`. -/
noncomputable def hypercoveringPushforwardComplexAllXIso (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (M : X.Modules) (n : ℕ) :
    ((hypercoveringPushforwardComplexAll f K).obj M).X (n : ℤ) ≅
      ∏ᶜ (fun i : (K.obj (op ⦋n⦌)).I ↦
        (pushforward (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f)).obj
          ((Scheme.Modules.pullback
            (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left)).obj M)) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
    (i := n) (i' := (n : ℤ)) (by simp)

/-- **The complex vanishes in negative degrees.**  This is the hypothesis `hT0` of
`StacksDraft.DerivedSectionsComparison`, which is what makes the complex comparable with a
bounded below right derived functor. -/
theorem isZero_hypercoveringPushforwardComplexAll_obj_X (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (M : X.Modules) (q : ℤ)
    (hq : q < 0) :
    IsZero (((hypercoveringPushforwardComplexAll f K).obj M).X q) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
    (fun i ↦ by simp only [ComplexShape.embeddingUpNat_f]; omega)

end Stacks.AlgebraicGeometry.UniversalPushforward

end
